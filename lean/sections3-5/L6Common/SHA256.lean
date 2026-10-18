/-!
# SHA-256

A plain implementation of SHA-256 (FIPS 180-4) over a byte array, used to identify the data files embedded with
`include_str` by their published checksums: `sha256Hex s` is the lowercase hexadecimal digest of the UTF-8 bytes of
the string `s`, as printed by `sha256sum`. The constants were computed with integer roots
(`scripts/f1/sha256_constants.py`); the implementation was tested against `sha256sum` on files of many lengths
(`logs/f1/sha256_test.log`).
-/

namespace L6.SHA256

/-- The round constants: the first 32 bits of the fractional parts of the cube roots of the first 64 primes. -/
def K : Array UInt32 := #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
  0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152,
  0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138,
  0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70,
  0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa,
  0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value: the first 32 bits of the fractional parts of the square roots of the first 8 primes. -/
def H0 : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
  0x5be0cd19]

/-- Rotation to the right by `r` bits (`0 < r < 32`). -/
def rotr (x r : UInt32) : UInt32 := (x >>> r) ||| (x <<< (32 - r))

/-- The padded message: the bytes of `m`, the byte `0x80`, zero bytes up to a length `≡ 56 (mod 64)`, and the length
of `m` in bits as 8 bytes, most significant first. -/
def pad (m : ByteArray) : ByteArray := Id.run do
  let len := m.size
  let mut r := m.push 0x80
  for _ in [0:(119 - len % 64) % 64] do
    r := r.push 0
  let bits := 8 * len
  for i in [0:8] do
    r := r.push (bits / 2 ^ (8 * (7 - i)) % 256).toUInt8
  return r

/-- The big-endian 32-bit word at the byte offset `o`. -/
def word (b : ByteArray) (o : Nat) : UInt32 :=
  (b[o]!.toUInt32 <<< 24) ||| (b[o + 1]!.toUInt32 <<< 16) ||| (b[o + 2]!.toUInt32 <<< 8) ||| b[o + 3]!.toUInt32

/-- The compression of the 64-byte block at the offset `o` of `b` into the hash value `H`. -/
def compress (H : Array UInt32) (b : ByteArray) (o : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for t in [0:16] do
    w := w.push (word b (o + 4 * t))
  for t in [16:64] do
    let x := w[t - 15]!
    let y := w[t - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  let mut a := H[0]!
  let mut bb := H[1]!
  let mut c := H[2]!
  let mut d := H[3]!
  let mut e := H[4]!
  let mut f := H[5]!
  let mut g := H[6]!
  let mut h := H[7]!
  for t in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := h + S1 + ch + K[t]! + w[t]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& bb) ^^^ (a &&& c) ^^^ (bb &&& c)
    let t2 := S0 + maj
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := bb
    bb := a
    a := t1 + t2
  return #[H[0]! + a, H[1]! + bb, H[2]! + c, H[3]! + d, H[4]! + e, H[5]! + f, H[6]! + g, H[7]! + h]

/-- The SHA-256 hash value (eight 32-bit words) of the bytes `m`. -/
def hash (m : ByteArray) : Array UInt32 :=
  let p := pad m
  (List.range (p.size / 64)).foldl (fun H i => compress H p (64 * i)) H0

/-- The lowercase hexadecimal digit of `v < 16`. -/
def hexDigit (v : Nat) : Char := if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)

/-- A 32-bit word as eight hexadecimal digits. -/
def hexWord (x : UInt32) : String :=
  (List.range 8).foldl (fun s i => s.push (hexDigit (x.toNat / 16 ^ (7 - i) % 16))) ""

/-- The digest of the bytes `m` in hexadecimal (64 characters). -/
def sha256HexBytes (m : ByteArray) : String := (hash m).foldl (fun s x => s ++ hexWord x) ""

/-- **The SHA-256 digest of the UTF-8 bytes of `s`**, in lowercase hexadecimal. -/
def sha256Hex (s : String) : String := sha256HexBytes s.toUTF8

end L6.SHA256
