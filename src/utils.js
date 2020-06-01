/*
    Copyright 2019 0KIMS association.

    This file is part of websnark (Web Assembly zkSnark Prover).

    websnark is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    websnark is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with websnark. If not, see <https://www.gnu.org/licenses/>.
*/

const bigInt = require('big-integer')
const Circuit = require('snarkjs/src/circuit')
const bigInt2 = require('snarkjs/src/bigint')
const hexifyBigInts = require('../tools/stringifybigint').hexifyBigInts
const unhexifyBigInts = require('../tools/stringifybigint').unhexifyBigInts
const stringifyBigInts = require('../tools/stringifybigint').stringifyBigInts
const unstringifyBigInts = require('../tools/stringifybigint').unstringifyBigInts
const stringifyBigInts2 = require('snarkjs/src/stringifybigint').stringifyBigInts
const unstringifyBigInts2 = require('snarkjs/src/stringifybigint').unstringifyBigInts

function bigInt2BytesLE (_a, len) {
  const b = Array(len)
  let v = bigInt(_a)
  for (let i = 0; i < len; i++) {
    b[i] = v.and(0xFF).toJSNumber()
    v = v.shiftRight(8)
  }
  return b
}

function bigInt2U32LE (_a, len) {
  const b = Array(len)
  let v = bigInt(_a)
  for (let i = 0; i < len; i++) {
    b[i] = v.and(0xFFFFFFFF).toJSNumber()
    v = v.shiftRight(32)
  }
  return b
}

function convertWitness (witness) {
  const buffLen = witness.length * 32
  const buff = new ArrayBuffer(buffLen)
  const h = {
    dataView: new DataView(buff),
    offset: 0
  }
  const mask = bigInt2(0xFFFFFFFF)
  for (let i = 0; i < witness.length; i++) {
    for (let j = 0; j < 8; j++) {
      const v = Number(witness[i].shr(j * 32).and(mask))
      h.dataView.setUint32(h.offset, v, true)
      h.offset += 4
    }
  }
  return buff
}

function toHex32 (number) {
  let str = number.toString(16)
  while (str.length < 64) str = '0' + str
  return str
}

function toSolidityInput (proof) {
  const flatProof = unstringifyBigInts([
    proof.pi_a[0], proof.pi_a[1],
    proof.pi_b[0][1], proof.pi_b[0][0],
    proof.pi_b[1][1], proof.pi_b[1][0],
    proof.pi_c[0], proof.pi_c[1]
  ])
  const result = {
    proof: '0x' + flatProof.map(x => toHex32(x)).join('')
  }
  if (proof.publicSignals) {
    result.publicSignals = hexifyBigInts(unstringifyBigInts(proof.publicSignals))
  }
  return result
}

function genWitness (input, circuitJson) {
  const circuit = new Circuit(unstringifyBigInts2(circuitJson))
  const witness = circuit.calculateWitness(unstringifyBigInts2(input))
  const publicSignals = witness.slice(1, circuit.nPubInputs + circuit.nOutputs + 1)
  return { witness, publicSignals }
}

async function genWitnessAndProve (groth16, input, circuitJson, provingKey) {
  const witnessData = genWitness(input, circuitJson)
  const witnessBin = convertWitness(witnessData.witness)
  const result = await groth16.proof(witnessBin, provingKey)
  result.publicSignals = stringifyBigInts2(witnessData.publicSignals)
  return result
}

// tsu - additions for tornado cash.

const merkleTree = require('./lib/MerkleTree')
const assert = require('assert')
const circomlib = require('circomlib')
const Web3 = require('web3')
const crypto = require('crypto')

const MERKLE_TREE_HEIGHT = 20
const RPC_URL = 'https://kovan.infura.io/v3/0279e3bdf3ee49d0b547c643c2ef78ef'
const PRIVATE_KEY = 'F8004254B528D77D390CA3F969598C208C4A3C95D0491B6E11611232F20B4586' // 0xe45D59f09A3c84bD083EE8a3148075a392187ceF
const CONTRACT_ADDRESS = '0x8b3f5393ba08c24cc7ff5a66a832562aab7bc95f'// '0xD6a6AC46d02253c938B96D12BE439F570227aE8E'
const AMOUNT = '0.1'

/** Generate random number of specified byte length */
const rbigint = nbytes => bigInt2.leBuff2int(crypto.randomBytes(nbytes))

/** Compute pedersen hash */
const pedersenHash = data => circomlib.babyJub.unpackPoint(circomlib.pedersenHash.hash(data))[0]

/** BigNumber to hex string of specified length */
const toHex = (number, length = 32) => '0x' + (number instanceof Buffer ? number.toString('hex') : bigInt(number).toString(16)).padStart(length * 2, '0')

/**
 * Parses Tornado.cash note
 * @param noteString the note
 */
function parseNote (noteString) {
  const noteRegex = /tornado-(?<currency>\w+)-(?<amount>[\d.]+)-(?<netId>\d+)-0x(?<note>[0-9a-fA-F]{124})/g
  const match = noteRegex.exec(noteString)

  // we are ignoring `currency`, `amount`, and `netId` for this minimal example
  const buf = Buffer.from(match.groups.note, 'hex')
  const nullifier = bigInt2.leBuff2int(buf.slice(0, 31))
  const secret = bigInt2.leBuff2int(buf.slice(31, 62))
  const deposit = { nullifier, secret }
  deposit.preimage = Buffer.concat([deposit.nullifier.leInt2Buff(31), deposit.secret.leInt2Buff(31)])
  deposit.commitment = pedersenHash(deposit.preimage)
  deposit.nullifierHash = pedersenHash(deposit.nullifier.leInt2Buff(31))
  return deposit
}

/**
 * Generate merkle tree for a deposit.
 * Download deposit events from the contract, reconstructs merkle tree, finds our deposit leaf
 * in it and generates merkle proof
 * @param deposit Deposit object
 */
async function generateMerkleProof (deposit) {
  console.log('Getting contract state...')
  const events = await contract.getPastEvents('Deposit', { fromBlock: 0, toBlock: 'latest' })
  const leaves = events
    .sort((a, b) => a.returnValues.leafIndex - b.returnValues.leafIndex) // Sort events in chronological order
    .map(e => e.returnValues.commitment)
  const tree = new merkleTree(MERKLE_TREE_HEIGHT, leaves)

  // Find current commitment in the tree
  const depositEvent = events.find(e => e.returnValues.commitment === toHex(deposit.commitment))
  const leafIndex = depositEvent ? depositEvent.returnValues.leafIndex : -1

  // Validate that our data is correct (optional)
  const isValidRoot = await contract.methods.isKnownRoot(toHex(await tree.root())).call()
  const isSpent = await contract.methods.isSpent(toHex(deposit.nullifierHash)).call()
  assert(isValidRoot === true, 'Merkle tree is corrupted')
  assert(isSpent === false, 'The note is already spent')
  assert(leafIndex >= 0, 'The deposit is not found in the tree')

  // Compute merkle proof of our commitment
  return await tree.path(leafIndex)
}

/**
 * Generate SNARK proof for withdrawal
 * @param deposit Deposit object
 * @param recipient Funds recipient
 */
async function generateSnarkProof (deposit, recipient, groth16, proving_key) {
  // Compute merkle proof of our commitment
  const { root, path_elements, path_index } = await generateMerkleProof(deposit)
  // Prepare circuit input
  const input = {
    // Public snark inputs
    root: root,
    nullifierHash: deposit.nullifierHash,
    recipient: bigInt2(recipient),
    relayer: 0,
    fee: 0,
    refund: 0,

    // Private snark inputs
    nullifier: deposit.nullifier,
    secret: deposit.secret,
    pathElements: path_elements,
    pathIndices: path_index
  }

  console.log('Generating SNARK proof...')
  console.log(input)
  const proofData = await genWitnessAndProve(groth16, input, circuit, proving_key)
  const { proof } = toSolidityInput(proofData)

  const args = [
    toHex(input.root),
    toHex(input.nullifierHash),
    toHex(input.recipient, 20),
    toHex(input.relayer, 20),
    toHex(input.fee),
    toHex(input.refund)
  ]

  return { proof, args }
}

let web3, contract, netId, circuit
async function withdraw (note, recipient, groth16, proving_key) {
  web3 = new Web3(new Web3.providers.HttpProvider(RPC_URL, { timeout: 5 * 60 * 1000 }), null, { transactionConfirmationBlocks: 1 })
  netId = await web3.eth.net.getId()
  contract = new web3.eth.Contract(require('../build/contracts/ETHTornado.json').abi, CONTRACT_ADDRESS)
  circuit = require('../build/circuits/withdraw.json')
  const account = web3.eth.accounts.privateKeyToAccount('0x' + PRIVATE_KEY)
  web3.eth.accounts.wallet.add('0x' + PRIVATE_KEY)
  // eslint-disable-next-line require-atomic-updates
  web3.eth.defaultAccount = account.address
  console.log('Default address:', web3.eth.defaultAccount)
  const deposit = parseNote(note)
  console.log('recipient', recipient)
  const { proof, args } = await generateSnarkProof(deposit, recipient, groth16, proving_key)
  console.log('Sending withdrawal transaction...')
  const tx = await contract.methods.withdraw(proof, ...args).send({ from: web3.eth.defaultAccount, gas: 1e6 })
  console.log(`https://kovan.etherscan.io/tx/${tx.transactionHash}`)
  return tx
}

module.exports = { bigInt2BytesLE, bigInt2U32LE, toSolidityInput, genWitnessAndProve, withdraw }
