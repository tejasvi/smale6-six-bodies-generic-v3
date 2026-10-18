import L6F34.Ident
import L6F34.Point
import L6Common.LP
import L6Poly.Basic

/-!
# F3, F4: the checks of Proposition 5.3 per cell

For each stored cell of a class (a chunk of consecutive cells), exactly one of the following is verified:

* **single term** (Lemma 5.1, F3): the cell is listed in `data/f34/single/c<N>.txt` with an identity and a term `i`;
  the identity is one of §5.1, and for every other term `k` the system `Π + {e_k − e_i ≤ 0}` is pruned by a
  certificate that `Farkas.check` (Lemma 4.6) accepts: on all of `Π` the term `i` has strictly the least exponent;
* **core** (Lemma 5.2, F4): the cell is listed in `data/f4/links/c<N>.txt` with a certificate, a fixed mass `F` and
  the names of the core polynomials; for each name the argmin set `S` of the identity is constant on `Π` (base
  identities: `S` is part of the cell; rows `D`: no condition; secondary identities: `S` is guessed at a
  floating-point point of `Π` and certified by accepted certificates that `Π + {±(e_j − e_i) ≥ s}` is empty for
  `j ∈ S` and `Π + {e_k − e_i ≤ 0}` is empty for `k ∉ S`), and the initial form `Σ_{i∈S} cᵢ [gᵢ]`, computed here from
  the trees (times the lcm of its denominators, then `m_F = 1` if `F ≥ 0`), equals generator `i` of the certificate
  (read by `L6.Poly.parseCert`, the reading of the cofactor checks);
* **open**: the cell is one of the 43 listed in `data/cells/open43.tsv`.

`checkChunk` returns `true` iff every cell of the chunk passes and the numbers of cells of each kind are the given
ones.
-/

namespace L6.F34

open L6.Poly

/-! ## Initial forms as polynomials -/

/-- The polynomial variable of a cell variable name: `6 + j` for the `j`-th name of the link. -/
def varIdx (vars : Array String) (name : String) : Option Nat := (vars.idxOf? name).map (6 + ·)

/-- The leading coefficient of `z_p − z_q` (or `w`): the difference of the node coordinates of the children of the
meet that contain `p` and `q` (coordinate `0` for the first child, Lemma 4.2). -/
def Ctx.leadPoly (x : Ctx) (vars : Array String) (z : Bool) (p q : Nat) : Option Poly := do
  let t := if z then x.zt else x.wt
  let tag := if z then "X" else "Y"
  let v ← t.meet p q
  let cp ← t.childIdx v (t.leaf.getD p maxNode)
  let cq ← t.childIdx v (t.leaf.getD q maxNode)
  let coord (i : Nat) : Option Poly :=
    if i == 0 then some [] else (varIdx vars s!"{tag}{v}_{i}").map fun j => [(packExp [(j, 1)], (1 : Int))]
  let a ← coord cp
  let b ← coord cq
  some (add a (neg b))

/-- Twice the leading coefficient of a term, as a polynomial. -/
def Ctx.coefPoly (x : Ctx) (vars : Array String) (cf : Coef) : Option Poly := do
  let mut es : List (Nat × Nat) := cf.masses.map fun m => (m, 1)
  for (a, b, e) in cf.dvars do
    let j ← varIdx vars s!"D{a}_{b}"
    es := es ++ [(j, e)]
  if cf.evar then
    let j ← varIdx vars "E"
    es := es ++ [(j, 1)]
  let mut p : Poly := ofTerms [(cf.num, es)]
  if cf.massSum then p := mul p (ofTerms ((List.range 6).map fun m => ((1 : Int), [(m, 1)])))
  for (z, a, b) in cf.leads do
    let lp ← x.leadPoly vars z a b
    p := mul p lp
  some p

/-- The generator of an initial form `Σ_{i∈S} cᵢ [gᵢ]`: times the lcm of the denominators of its coefficients
(`1` or `2`), then `m_F = 1` if `F ≥ 0`, normalized. -/
def Ctx.genOf (x : Ctx) (vars : Array String) (ts : Array Term) (S : List Nat) (fixed : Int) : Option Poly := do
  let mut p2 : Poly := []
  for s in S do
    let t ← ts[s]?
    let q ← x.coefPoly vars t.coef
    p2 := add p2 q
  let g := if p2.all (fun t => t.2 % 2 == 0) then p2.map (fun t => (t.1, t.2 / 2)) else p2
  let g := if 0 ≤ fixed then substOne fixed.toNat g else g
  some (normalize g)

/-- The generator of the row `D_kl² z_kl w_kl − 1`. -/
def Ctx.distGen (x : Ctx) (vars : Array String) (k l : Nat) : Option Poly := do
  let j ← varIdx vars s!"D{k}_{l}"
  let lz ← x.leadPoly vars true k l
  let lw ← x.leadPoly vars false k l
  some (normalize (add (mul (ofTerms [((1 : Int), [(j, 2)])]) (mul lz lw)) (ofTerms [((-1 : Int), [])])))

/-! ## Certified argmin decisions -/

/-- The system `Π` plus the row `r` is pruned: `Farkas.check` (Lemma 4.6) accepts the certificate that the
floating-point proposer finds for it. -/
def prunedWith (nh : Nat) (rows : Array Row) (r : Row) : Bool :=
  let rs := rows.push r
  Farkas.check nh rs (L6.LP.decide rs nh).cert

/-- The row `e_k − e_i ≤ 0` (data times 2). -/
def rowLe (ts : Array Term) (k i : Nat) : Row := { a := vsub ts[k]!.expo ts[i]!.expo, c := 0, lo := none, hi := some 0 }

/-- The row `e_k − e_i − s ≥ 0` (data times 2). -/
def rowGeS (ts : Array Term) (k i : Nat) : Row := { a := vsub ts[k]!.expo ts[i]!.expo, c := -2, lo := some 0, hi := none }

/-- On `Π`, the term `i` has strictly the least exponent among the terms `ts`: for every other term `k`, the system
`Π + {e_k − e_i ≤ 0}` has an accepted certificate. -/
def strictlyLeast (nh : Nat) (rows : Array Row) (ts : Array Term) (i : Nat) : Bool :=
  (List.range ts.size).all fun k => k == i || prunedWith nh rows (rowLe ts k i)

/-- The argmin set `S` (with `i₀ = S[0]`) is constant on `Π`: for `j ∈ S`, `Π + {e_j − e_{i₀} ≥ s}` and
`Π + {e_{i₀} − e_j ≥ s}` have accepted certificates; for `k ∉ S`, `Π + {e_k − e_{i₀} ≤ 0}` has one. -/
def constantArgmin (nh : Nat) (rows : Array Row) (ts : Array Term) (S : List Nat) : Bool :=
  match S with
  | [] => false
  | i0 :: _ =>
    (List.range ts.size).all fun k =>
      k == i0 ||
      (if S.contains k then prunedWith nh rows (rowGeS ts k i0) && prunedWith nh rows (rowGeS ts i0 k)
       else prunedWith nh rows (rowLe ts k i0))

/-- The argmin set guessed at the floating-point point `pt` (tolerance `1e-7` on exponents, as the engine). -/
def guessArgmin (pt : Array Float) (ts : Array Term) : List Nat :=
  let val (t : Term) : Float := (List.range t.expo.size).foldl
    (fun acc j => acc + Float.ofInt t.expo[j]! * pt.getD j 0.0) 0.0 / 2.0
  let vs := ts.map val
  let mn := vs.foldl min (vs.getD 0 0.0)
  (List.range ts.size).filter fun k => Float.abs (vs[k]! - mn) < 1e-7

/-! ## Data files -/

/-- A link line: class, cell, certificate id, fixed mass, names, variables. -/
structure Link where
  cls : Nat
  cell : Nat
  cert : String
  fixed : Int
  names : Array String
  vars : Array String
  deriving Inhabited

def parseLink (line : String) : Option Link := do
  let ws := (line.splitOn " ").filter (· ≠ "")
  let (pre, post) := ws.span (· ≠ "|")
  match pre with
  | c :: cell :: cert :: f :: names =>
    some { cls := ← c.toNat?, cell := ← cell.toNat?, cert, fixed := ← f.toInt?, names := names.toArray,
           vars := (post.drop 1).toArray }
  | _ => none

/-- Nonempty lines. -/
def lines (s : String) : List String := (s.splitOn "\n").filter (· ≠ "")

/-- The open cells of a class (`class CC cell` lines; `#` comments). -/
def openCells (cls : Nat) (s : String) : List Nat :=
  (lines s).filterMap fun l =>
    if l.startsWith "#" then none
    else match (l.splitOn "\t") with
      | [c, _, cell] => if c.toNat? == some cls then cell.toNat? else none
      | _ => none

/-- The number of cells of a stored file. -/
def numCells (cellsTxt : String) : Nat := (lines cellsTxt).length

/-! ## Per cell -/

/-- The base identities (`(z,S,(k,))`, `(U,)`, `(I,)`), whose argmin sets are part of the cell. -/
def isBase : IdName → Bool
  | .body .. | .U | .I => true
  | _ => false

/-- The generator of a base identity: its argmin set is the cell's. -/
def genBase (x : Ctx) (c : Cell) (lk : Link) (nm : IdName) : Option Poly := do
  let ts ← x.baseTerms nm
  let (_, labs) ← c.argmin.find? (·.1 == nm)
  let S ← labs.mapM (findLab ts)
  x.genOf lk.vars ts S.toList lk.fixed

/-- The generator of a secondary identity: its argmin set, guessed at `pt`, must be certified constant on `Π`. -/
def genSec (x : Ctx) (rows : Array Row) (pt : Array Float) (lk : Link) (nm : IdName) : Option Poly := do
  let ts ← x.secTerms nm
  let S := guessArgmin pt ts
  if constantArgmin x.nh rows ts S then x.genOf lk.vars ts S lk.fixed else none

/-- The generator of the core polynomial named `nmS` of the cell, if its initial form is certified on the cell. -/
def genFor (x : Ctx) (c : Cell) (rows : Array Row) (pt : Array Float) (lk : Link) (nmS : String) : Option Poly :=
  match IdName.parse nmS with
  | none => none
  | some (.dist k l) => if k < l && l < 6 then x.distGen lk.vars k l else none
  | some nm => if isBase nm then genBase x c lk nm else genSec x rows pt lk nm

/-- F3 for one cell. -/
def checkSingle (x : Ctx) (rows : Array Row) (nm : IdName) (lab : Lab) : Bool :=
  match x.secTerms nm with
  | none => false
  | some ts =>
    match findLab ts lab with
    | none => false
    | some i => strictlyLeast x.nh rows ts i

/-- F4 for one cell: the certificate has the link's variables and fixed mass, and each of its generators is the
certified initial form of the corresponding name. -/
def checkLink (x : Ctx) (c : Cell) (rows : Array Row) (pt : Array Float) (lk : Link) (cert : Cert) : Bool :=
  cert.nvar == lk.vars.size && cert.fixed == lk.fixed && cert.gens.length == lk.names.size &&
  (List.range lk.names.size).all fun i => genFor x c rows pt lk lk.names[i]! == some (normalize cert.gens[i]!)

/-- The parsed inputs of a class. -/
structure ChunkData where
  dg : Diagram
  cells : Array String
  ncells : Nat
  opens : List Nat
  single : Array (Option (IdName × Lab))
  links : Array (Option Link)
  pass : Array Nat
  certs : List (String × Cert)
  deriving Inhabited

/-- The certificates, read by `L6.Poly.parseCert` (all must parse). -/
def parseAll : List (String × String) → Option (List (String × Cert))
  | [] => some []
  | (id, txt) :: rest => do
    let c ← parseCert txt
    let r ← parseAll rest
    some ((id, c) :: r)

/-- Reads the single-term list, the links and the pass tags of a class with `ncells` cells. -/
def readLists (cls ncells : Nat) (singleTxt linksTxt passTxt : String) :
    Option (Array (Option (IdName × Lab)) × Array (Option Link) × Array Nat) := do
  let mut single : Array (Option (IdName × Lab)) := Array.replicate ncells none
  for l in lines singleTxt do
    match (l.splitOn " ") with
    | [c, nm, lab] =>
      let c ← c.toNat?
      let nm ← IdName.parse nm
      let lab ← Lab.parse lab
      if c ≥ ncells || (single[c]!).isSome then none
      single := single.set! c (some (nm, lab))
    | _ => none
  let mut links : Array (Option Link) := Array.replicate ncells none
  for l in lines linksTxt do
    let lk ← parseLink l
    if lk.cls != cls || lk.cell ≥ ncells || (links[lk.cell]!).isSome then none
    links := links.set! lk.cell (some lk)
  let mut pass : Array Nat := Array.replicate ncells 0
  for l in lines passTxt do
    match (l.splitOn " ") with
    | [c, p] =>
      let c ← c.toNat?
      let p ← p.toNat?
      if c ≥ ncells then none
      pass := pass.set! c p
    | _ => none
  some (single, links, pass)

/-- Reads the inputs of class `cls` (class representative, certificates, cell lines, lists, open cells). -/
def prepare (cls : Nat) (n6 cellsTxt singleTxt linksTxt passTxt openTxt : String) (certs : List (String × String)) :
    Option ChunkData := do
  let n6j ← (Lean.Json.parse n6).toOption
  let dg ← Diagram.ofN6 n6j cls
  let parsed ← parseAll certs
  let cl := (cellsTxt.splitOn "\n").toArray
  let ncells := if cl.back? == some "" then cl.size - 1 else cl.size
  let (single, links, pass) ← readLists cls ncells singleTxt linksTxt passTxt
  some { dg, cells := cl, ncells, opens := openCells cls openTxt, single, links, pass, certs := parsed }

/-- The context of cell `idx`: the cell, its rows, and a floating-point point of it (the guard that the encoded cell is
not empty; not needed for soundness). -/
def cellCtx (cd : ChunkData) (idx : Nat) : Option (Ctx × Cell × Array Row × Array Float) := do
  let j ← (Lean.Json.parse (cd.cells.getD idx "")).toOption
  let c ← Cell.ofJson j
  let x := Ctx.mk' cd.dg c
  let rows ← x.cellRows c
  let pt ← interiorPoint rows x.nh
  some (x, c, rows, pt)

/-- The number of lists (open, single term, core link) that contain cell `idx`. -/
def kindsOf (cd : ChunkData) (idx : Nat) : Nat :=
  (if cd.opens.contains idx then 1 else 0) + (if (cd.single.getD idx none).isSome then 1 else 0) +
    (if (cd.links.getD idx none).isSome then 1 else 0)

/-- The kind of a core cell from its pass tag: `2` first pass, `3` second pass, `0` otherwise. -/
def passKind : Nat → Nat
  | 1 => 2
  | 2 => 3
  | _ => 0

/-- The kind of cell `idx` if it passes: `1` single term, `2` core (first pass), `3` core (second pass), `4` open;
`0` if it fails. Exactly one of the three lists must contain the cell. -/
def cellKind (cd : ChunkData) (idx : Nat) : Nat :=
  if kindsOf cd idx != 1 then 0
  else if cd.opens.contains idx then 4
  else
    match cellCtx cd idx with
    | none => 0
    | some (x, c, rows, pt) =>
      match cd.single.getD idx none, cd.links.getD idx none with
      | some (nm, lab), _ => if checkSingle x rows nm lab then 1 else 0
      | none, some lk =>
        match cd.certs.lookup lk.cert with
        | none => 0
        | some cert => if checkLink x c rows pt lk cert then passKind (cd.pass.getD idx 0) else 0
      | none, none => 0

structure Counts where
  single : Nat := 0
  core1 : Nat := 0
  core2 : Nat := 0
  opn : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def countKinds (ks : List Nat) : Counts :=
  ks.foldl (fun cnt k =>
    match k with
    | 1 => { cnt with single := cnt.single + 1 }
    | 2 => { cnt with core1 := cnt.core1 + 1 }
    | 3 => { cnt with core2 := cnt.core2 + 1 }
    | 4 => { cnt with opn := cnt.opn + 1 }
    | _ => cnt) {}

/-- **The checker of a chunk**: the inputs parse, `lo ≤ hi ≤` the number of cells, every cell `lo ≤ idx < hi`
passes (`cellKind ≠ 0`), and the numbers of cells of each kind are the given ones. -/
def checkChunk (cls : Nat) (n6 cellsTxt singleTxt linksTxt passTxt openTxt : String)
    (certs : List (String × String)) (lo hi : Nat) (expected : Counts) : Bool :=
  match prepare cls n6 cellsTxt singleTxt linksTxt passTxt openTxt certs with
  | none => false
  | some cd =>
    let ks := (List.range' lo (hi - lo)).map (cellKind cd)
    decide (lo ≤ hi) && decide (hi ≤ cd.ncells) && ks.all (· != 0) && decide (countKinds ks = expected)

/-! ## Diagnostics (development only; not used by the checks) -/

/-- The first failing cell of a chunk with a reason, or the counts. -/
def explainChunk (cls : Nat) (n6 cellsTxt singleTxt linksTxt passTxt openTxt : String)
    (certs : List (String × String)) (lo hi : Nat) : Except String Counts := do
  let some cd := prepare cls n6 cellsTxt singleTxt linksTxt passTxt openTxt certs | throw "inputs do not parse"
  if hi > cd.ncells || lo > hi then throw "chunk out of range"
  let ks := (List.range' lo (hi - lo)).map (cellKind cd)
  for idx in List.range' lo (hi - lo) do
    if cellKind cd idx == 0 then
      let some (x, c, rows, pt) := cellCtx cd idx | throw s!"cell {idx}: cell, rows or interior point"
      match cd.single.getD idx none, cd.links.getD idx none with
      | some _, _ => throw s!"cell {idx}: single term not certified (or listed twice)"
      | none, some lk =>
        let some cert := cd.certs.lookup lk.cert | throw s!"cell {idx}: certificate {lk.cert} missing"
        for i in [0:lk.names.size] do
          if genFor x c rows pt lk lk.names[i]! != some (normalize cert.gens.toArray[i]!) then
            throw s!"cell {idx}: generator {i} ({lk.names[i]!}) differs or is not certified"
        throw s!"cell {idx}: link header or pass tag"
      | none, none => throw s!"cell {idx}: in no list"
  return countKinds ks

end L6.F34
