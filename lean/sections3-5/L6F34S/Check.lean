import L6F2S.Stored
import L6F34.Check
import L6F34.Point
import L6F34S.Ids

/-!
# F3, F4 on the cells of the specification search

The checks of Proposition 5.3 (`L6F34`), redone on the objects of the completeness theorem of Proposition 4.5
(`L6F2S`), so that their meaning can be stated for every pair of complete trees with heights satisfying `Cond`:

* the cell of a stored line is taken from the specification search itself: `cellsBelowR` lists, for a complete pair
  of trees, the argmin parts of its cells together with the rows of each cell (the rows of the pair, the forced
  argmin sets, and the rows of the argmin choices of the other base identities);
* the exponent of a term of an identity of `L6F34S.Ids` is a form over the heights of the pair (`termForm`, twice the
  exponent; `none` when a factor vanishes, exponent `⊤`);
* **single term** (Lemma 5.1): for the identity and term named in `data/f34/single/c<N>.txt`, every other term with
  a finite exponent has a strictly larger exponent on the cell (an accepted certificate for `Π + {e_k − e_i ≤ 0}`);
* **core** (Lemma 5.2): for each name of the link in `data/f4/links/c<N>.txt`, the argmin set `S` of the identity,
  guessed at a floating-point point of the cell, is certified constant on the cell, and the initial form, written
  from the trees as a polynomial in the variables of the certificate (`itemPoly`, `distPoly`), is its generator.

The variables of a certificate are the masses and the link's names: `X{v}_{i}` (`Y{v}_{i}`) is the node coordinate of
child `i` of the engine's node `v` of the `z` (`w`) tree, with child `0` the base (coordinate `0`, Lemma 4.2); `D{k}_{l}`
is the leading coefficient of `p_kl`; `E` the energy. Each name is read once into the masks of the node, the child and
the base child (`VarM`); the initial forms are written through these masks, so that a node coordinate of the
certificate stands for the difference of two node coordinates (child minus base child) whatever base the reader of
the theorem uses.
-/

namespace L6.F34S

open L6.F2S (TS Pair form fsub keepLP partialRows idents splitForced comOk all argminRec SIdent nodeMask between
  jPairs? keyOfLine)
open L6.F2 (Diag Label renderEntry)
open L6.F34 (Lab IdName Link prunedWith)
open L6.Poly
open Lean

/-! ## Exponent forms on a pair of trees -/

/-- The coefficients of twice the exponent of a factor `z_p − z_q` (`z = true`) or `w_p − w_q`: `2` at the variable of
the lowest common ancestor; `none` if `p` and `q` share a leaf (the factor vanishes). -/
def sepCoefs (P : Pair) (z : Bool) (pq : Nat × Nat) : Option (List (Nat × Int)) :=
  let T := if z then P.tz else P.tw
  if T.sameLeaf pq.1 pq.2 then none
  else
    match T.lca pq.1 pq.2 with
    | some C => some [((if z then P.vz C else P.vw C), 2)]
    | none => some []

/-- The coefficients of twice the exponent of `p_kl`: `−1` at the lowest common ancestors of `k`, `l` in both trees. -/
def pCoefs (P : Pair) (kl : Nat × Nat) : List (Nat × Int) :=
  (match P.tz.lca kl.1 kl.2 with | some C => [(P.vz C, -1)] | none => []) ++
    (match P.tw.lca kl.1 kl.2 with | some C => [(P.vw C, -1)] | none => [])

/-- Twice the exponent of a term as a form over the heights of the pair; `none` if a factor vanishes. -/
def termForm (P : Pair) (t : XTerm) : Option (Array Int) := do
  let zs ← t.zs.mapM (sepCoefs P true)
  let ws ← t.ws.mapM (sepCoefs P false)
  some (form P.nv (zs.flatten ++ ws.flatten ++ (t.ps.map (pCoefs P)).flatten))

/-! ## The cells of a complete pair with their rows -/

/-- `branchRec` of the specification search, keeping the rows of each choice. -/
def branchRecR (keep : Array Row → Bool) (L0 : Array Row) :
    List SIdent → Array Row → List String → List (List String × Array Row)
  | [], extra, chosen => [(chosen, extra)]
  | id :: rest, extra, chosen =>
    (argminRec keep (L0 ++ extra) id.terms id.terms.length 0 none [] [] #[]).flatMap fun Sr =>
      branchRecR keep L0 rest (extra ++ Sr.2)
        (chosen ++ [renderEntry id.name (Sr.1.map fun t => id.labels.getD t .E).toArray])

/-- `cellsBelow` of the specification search, keeping the rows of each cell: the argmin part of the line and the rows
of the cell (rows of the pair, forced argmin sets, argmin choices). -/
def cellsBelowR (keep : Array Row → Nat → Bool) (D : Diag) (P : Pair) : List (String × Array Row) :=
  if !(comOk P.tz all && comOk P.tw all) then [] else
  match partialRows D P all, idents D P with
  | some L0, some ids =>
    if !keep L0 P.nv then [] else
    match splitForced ids with
    | none => []
    | some (extra, fixed, branch) =>
      if !keep (L0 ++ extra) P.nv then [] else
      (branchRecR (fun r => keep r P.nv) L0 branch extra []).map fun cr =>
        (", ".intercalate (fixed ++ cr.1), L0 ++ cr.2)
  | _, _ => []

/-- The pair of trees with the given keys. -/
def pairOfKeys (kz kw : List Nat × Option Nat) : Pair := ⟨⟨kz.1, kz.2⟩, ⟨kw.1, kw.2⟩⟩

/-! ## Single terms and constant argmin sets -/

/-- The row `a − b ≤ 0` (data already doubled). -/
def rowLe (a b : Array Int) : Row := { a := fsub a b, c := 0, lo := none, hi := some 0 }

/-- The row `a − b ≥ s` (data already doubled). -/
def rowGeS (a b : Array Int) : Row := { a := fsub a b, c := -2, lo := some 0, hi := none }

/-- On the cell, term `i` has a finite exponent strictly smaller than that of every other term with a finite
exponent. -/
def strictlyLeastS (nv : Nat) (rows : Array Row) (fs : List (Option (Array Int))) (i : Nat) : Bool :=
  match fs.getD i none with
  | none => false
  | some fi =>
    (List.range fs.length).all fun k =>
      k == i ||
      match fs.getD k none with
      | none => true
      | some fk => prunedWith nv rows (rowLe fk fi)

/-- The argmin set `S` (first element `i₀`) is constant on the cell: the terms of `S` have finite exponents equal to
that of `i₀`, and every other term with a finite exponent has a larger one (terms with exponent `⊤` are not in `S`). -/
def constantArgminS (nv : Nat) (rows : Array Row) (fs : List (Option (Array Int))) (S : List Nat) : Bool :=
  match S with
  | [] => false
  | i0 :: _ =>
    match fs.getD i0 none with
    | none => false
    | some f0 =>
      S.all (· < fs.length) &&
      (List.range fs.length).all fun k =>
        k == i0 ||
        match fs.getD k none with
        | none => !S.contains k
        | some fk =>
          if S.contains k then prunedWith nv rows (rowGeS fk f0) && prunedWith nv rows (rowGeS f0 fk)
          else prunedWith nv rows (rowLe fk f0)

/-- The argmin set guessed at the floating-point point `pt` (tolerance `1e-7` on exponents), among the terms with a
finite exponent. -/
def guessArgminS (pt : Array Float) (fs : List (Option (Array Int))) : List Nat :=
  let val (f : Array Int) : Float :=
    (List.range f.size).foldl (fun acc j => acc + Float.ofInt f[j]! * pt.getD j 0.0) 0.0 / 2.0
  let vs : List (Option Float) := fs.map (·.map val)
  let mn := vs.foldl (fun acc v => match v with | some x => min acc x | none => acc) 1.0e300
  (List.range fs.length).filter fun k =>
    match vs.getD k none with
    | some x => Float.abs (x - mn) < 1e-7
    | none => false

/-! ## The variables of a certificate -/

/-- A tree of a stored line by the engine's node numbers: for each internal node, its number, the set of the points
below it and those of its children, in the stored order. -/
abbrev ETree := List (Nat × Nat × List Nat)

/-- Reads the engine tree of a stored line (`{"children": {...}, "leaf": {...}, "root": r}`). -/
def etreeOfJson (j : Json) : Option ETree := do
  let ch ← (j.getObjVal? "children").toOption
  let lf ← (j.getObjVal? "leaf").toOption
  let chs ← jPairs? ch
  let lfs ← jPairs? lf
  let children ← chs.mapM fun (k, v) => do
    let kv ← k.toNat?
    let arr ← (v.getArr?).toOption
    let cs ← arr.toList.mapM fun x => (x.getNat?).toOption
    some (kv, cs)
  let leaf ← lfs.mapM fun (k, v) => do
    let kv ← k.toNat?
    let lv ← (v.getNat?).toOption
    some (kv, lv)
  some (children.map fun (v, cs) => (v, nodeMask children leaf 16 v, cs.map (nodeMask children leaf 16)))

/-- The engine trees of a stored line. -/
def etreesOfLine (line : String) : Option (ETree × ETree) := do
  let zt ← between line "\"ztree\": " ", \"wtree\": "
  let wt ← between line "\"wtree\": " ", \"argmin\": ["
  let zj ← (Json.parse zt).toOption
  let wj ← (Json.parse wt).toOption
  some (← etreeOfJson zj, ← etreeOfJson wj)

/-- A variable of a certificate after reading: node coordinate of the child `c` of the node `v` with base child `c0`
(sets of points) in the `z` or `w` tree, the leading coefficient of `p_kl`, the energy, or unreadable. -/
inductive VarM where
  | X (v c c0 : Nat) | Y (v c c0 : Nat) | D (k l : Nat) | E | bad
  deriving DecidableEq, Inhabited, Repr

/-- The masks of child `i` and child `0` of the engine node `v`. -/
def childMasks (et : ETree) (v i : Nat) : Option (Nat × Nat × Nat) := do
  let (_, vm, cs) ← et.find? (·.1 == v)
  let c ← cs[i]?
  let c0 ← cs[0]?
  some (vm, c, c0)

/-- Reads a variable name of a link (`X7_1`, `Y8_2`, `D0_4`, `E`). -/
def readVar (ez ew : ETree) (s : String) : VarM :=
  let body : String := (s.drop 1).toString
  let two : Option (Nat × Nat) := match body.splitOn "_" with
    | [a, b] => do some (← a.toNat?, ← b.toNat?)
    | _ => none
  if s == "E" then .E
  else if s.startsWith "X" then
    match two.bind fun (v, i) => childMasks ez v i with
    | some (vm, c, c0) => .X vm c c0
    | none => .bad
  else if s.startsWith "Y" then
    match two.bind fun (v, i) => childMasks ew v i with
    | some (vm, c, c0) => .Y vm c c0
    | none => .bad
  else if s.startsWith "D" then
    match two with
    | some (k, l) => .D k l
    | none => .bad
  else .bad

/-! ## Initial forms as polynomials -/

/-- An unpacked polynomial: terms `(coefficient, monomial as (variable, exponent) pairs)`. -/
abbrev UPoly := List (Int × List (Nat × Nat))

def UPoly.mul (p q : UPoly) : UPoly := p.flatMap fun a => q.map fun b => (a.1 * b.1, a.2 ++ b.2)

def UPoly.prod (ps : List UPoly) : UPoly := ps.foldr UPoly.mul [(1, [])]

def UPoly.neg (p : UPoly) : UPoly := p.map fun a => (-a.1, a.2)

def UPoly.var (v : Nat) : UPoly := [(1, [(v, 1)])]

/-- Sets the variable `F` to `1` (if `F ≥ 0`). -/
def UPoly.substOne (F : Int) (p : UPoly) : UPoly :=
  if F < 0 then p else p.map fun a => (a.1, a.2.filter fun ve => ve.1 != F.toNat)

/-- The total exponent of the variable `i` in a monomial. -/
def degIn (mono : List (Nat × Nat)) (i : Nat) : Nat := (mono.filter (·.1 == i)).foldl (fun s ve => s + ve.2) 0

/-- Every variable of every monomial is `< nv`, with total exponent `< 128` (so packing does not overflow). -/
def UPoly.small (nv : Nat) (p : UPoly) : Bool :=
  p.all fun a => a.2.all (·.1 < nv) && (List.range nv).all fun i => degIn a.2 i < 128

/-- The packed normal form. -/
def UPoly.pack (p : UPoly) : Poly := normalize (p.map fun a => (packExp a.2, a.1))

/-- The step of `pickMax`: keep the larger (for inclusion) of the accumulator and the current element, among the
elements satisfying `P`. -/
def pickMaxStep (P : Nat → Bool) (acc : Option Nat) (C : Nat) : Option Nat :=
  if P C then
    match acc with
    | none => some C
    | some D => if L6.F2S.subset D C then some C else some D
  else acc

/-- The largest element (for inclusion) among the elements of `L` satisfying `P`. -/
def pickMax (P : Nat → Bool) (L : List Nat) : Option Nat := L.foldl (pickMaxStep P) none

/-- The largest node of `T` strictly inside `v` containing `p`, or the leaf class of `p`: the child of `v` that
contains `p`. -/
def childOf (T : TS) (v p : Nat) : Nat :=
  match pickMax (fun C => L6.F2S.ssubset C v && L6.F2S.mem p C) T.nodes with
  | some C => C
  | none => T.leafClass p

/-- The context of the polynomial of a cell: the pair of trees, the engine trees and the variables of the link. -/
structure PCtx where
  P : Pair
  ez : ETree
  ew : ETree
  vars : Array VarM

/-- The position of the variable `x` in the variables of the link. -/
def findVar (vars : Array VarM) (x : VarM) : Option Nat := (List.range vars.size).find? fun j => vars[j]! == x

/-- The base child of the node with mask `v` in an engine tree. -/
def baseChild (et : ETree) (v : Nat) : Option Nat := do
  let (_, _, cs) ← et.find? (·.2.1 == v)
  cs[0]?

/-- The node coordinate of the child `c` of the node `v` minus that of the base child: `0` for the base child, else
the variable of the link that names it. -/
def coordU (x : PCtx) (z : Bool) (v c : Nat) : Option UPoly :=
  match baseChild (if z then x.ez else x.ew) v with
  | none => none
  | some c0 =>
    if c == c0 then some []
    else
      match findVar x.vars (if z then VarM.X v c c0 else VarM.Y v c c0) with
      | none => none
      | some j => some (UPoly.var (6 + j))

/-- The leading coefficient of `z_p − z_q` (or `w`): the difference of the node coordinates of the children of the
lowest common ancestor that contain `p` and `q`. -/
def lcU (x : PCtx) (z : Bool) (pq : Nat × Nat) : Option UPoly :=
  match (if z then x.P.tz else x.P.tw).lca pq.1 pq.2 with
  | none => none
  | some v =>
    match coordU x z v (childOf (if z then x.P.tz else x.P.tw) v pq.1),
        coordU x z v (childOf (if z then x.P.tz else x.P.tw) v pq.2) with
    | some a, some b => some (a ++ b.neg)
    | _, _ => none

/-- The leading coefficient of `p_kl`. -/
def dU (x : PCtx) (kl : Nat × Nat) : Option UPoly :=
  match findVar x.vars (VarM.D (min kl.1 kl.2) (max kl.1 kl.2)) with
  | none => none
  | some j => some (UPoly.var (6 + j))

/-- Twice the numerical coefficient, the masses and the energy `ev` of a coefficient. -/
def coefBase (c : XCoef) (ev : List (Nat × Nat)) : UPoly := [(2 * c.num / c.den, c.masses.map (·, 1) ++ ev)]

/-- Times the sum of the masses, if `msum`. -/
def withMassSum (msum : Bool) (u : UPoly) : UPoly :=
  if msum then u.mul ((List.range 6).map fun k => (1, [(k, 1)])) else u

/-- Twice a coefficient. -/
def coefU2 (x : PCtx) (c : XCoef) : Option UPoly :=
  if c.e then
    match findVar x.vars VarM.E with
    | none => none
    | some j => some (withMassSum c.msum (coefBase c [(6 + j, 1)]))
  else some (withMassSum c.msum (coefBase c []))

/-- Twice the leading coefficient of a term. -/
def termU2 (x : PCtx) (t : XTerm) : Option UPoly :=
  match coefU2 x t.coef, t.zs.mapM (lcU x true), t.ws.mapM (lcU x false), t.ps.mapM (dU x) with
  | some c, some zs, some ws, some ds => some (UPoly.prod (c :: zs ++ ws ++ ds))
  | _, _, _, _ => none

/-- Halves the coefficients if they are all even; the flag says whether it did. -/
def halve (p : Poly) : Poly × Bool :=
  if p.all (fun t => t.2 % 2 == 0) then (p.map fun t => (t.1, t.2 / 2), true) else (p, false)

/-- Twice the initial form `Σ_{i∈S} cᵢ lc(gᵢ)` times the engine's factor of the identity, with `m_F = 1` when a mass
is fixed, unpacked. -/
def itemU (x : PCtx) (I : XId) (S : List Nat) (fixed : Int) : Option UPoly :=
  match S.mapM fun i => (I.terms[i]?).bind (termU2 x) with
  | none => none
  | some ts => some (((UPoly.prod (I.scale.map UPoly.var)).mul ts.flatten).substOne fixed)

/-- The generator of an initial form: `itemU` packed, halved when all coefficients are even. -/
def itemPoly (x : PCtx) (I : XId) (S : List Nat) (fixed : Int) : Option Poly :=
  match itemU x I S fixed with
  | none => none
  | some u => if u.small (6 + x.vars.size) then some (normalize (halve u.pack).1) else none

/-- `D_kl² z_kl w_kl − 1`, unpacked. -/
def distU (d a b : UPoly) : UPoly := UPoly.prod [d, d, a, b] ++ [(-1, [])]

/-- The generator of the row `D_kl² z_kl w_kl − 1`. -/
def distPoly (x : PCtx) (k l : Nat) : Option Poly :=
  match dU x (k, l), lcU x true (k, l), lcU x false (k, l) with
  | some d, some a, some b =>
    if (distU d a b).small (6 + x.vars.size) then some (distU d a b).pack else none
  | _, _, _ => none

/-- The generator of the initial form of the identity `nm`, if its argmin set is certified constant on the cell. -/
def genItem (x : PCtx) (rows : Array Row) (pt : Array Float) (fixed : Int) (nm : IdName) : Option Poly :=
  match XId.ofName nm with
  | none => none
  | some I =>
    if I.good then
      if constantArgminS x.P.nv rows (I.terms.map (termForm x.P)) (guessArgminS pt (I.terms.map (termForm x.P)))
      then itemPoly x I (guessArgminS pt (I.terms.map (termForm x.P))) fixed
      else none
    else none

/-- The generator of the core polynomial named `nmS`. -/
def genForS (x : PCtx) (rows : Array Row) (pt : Array Float) (fixed : Int) (nmS : String) : Option Poly :=
  match IdName.parse nmS with
  | none => none
  | some (.dist k l) => if k < l && l < 6 then distPoly x k l else none
  | some nm => genItem x rows pt fixed nm

/-! ## Per cell -/

/-- F3 for one cell: the named identity is valid and its named term has strictly the least exponent. -/
def checkSingleS (P : Pair) (rows : Array Row) (nm : IdName) (lab : Lab) : Bool :=
  match XId.ofName nm with
  | none => false
  | some I =>
    I.good &&
    match findLabX I.terms lab with
    | none => false
    | some i => strictlyLeastS P.nv rows (I.terms.map (termForm P)) i

/-- F4 for one cell: the certificate has the link's variables and fixed mass, and each generator is the certified
initial form of its name. -/
def checkLinkS (x : PCtx) (rows : Array Row) (pt : Array Float) (lk : Link) (cert : Cert) : Bool :=
  cert.nvar == lk.vars.size && cert.fixed == lk.fixed && decide (lk.fixed < 6) && cert.gens.length == lk.names.size &&
  (List.range lk.names.size).all fun i => genForS x rows pt lk.fixed lk.names[i]! == some (normalize cert.gens[i]!)

/-- The parsed inputs of a class. -/
structure ChunkDataS where
  D : Diag
  cells : Array String
  ncells : Nat
  opens : List Nat
  single : Array (Option (IdName × Lab))
  links : Array (Option Link)
  pass : Array Nat
  certs : List (String × Cert)
  deriving Inhabited

/-- Reads the inputs of class `cls`. -/
def prepareS (cls : Nat) (D : Diag) (cellsTxt singleTxt linksTxt passTxt openTxt : String)
    (certs : List (String × String)) : Option ChunkDataS := do
  let parsed ← L6.F34.parseAll certs
  let cl := (cellsTxt.splitOn "\n").toArray
  let ncells := if cl.back? == some "" then cl.size - 1 else cl.size
  let (single, links, pass) ← L6.F34.readLists cls ncells singleTxt linksTxt passTxt
  some { D, cells := cl, ncells, opens := L6.F34.openCells cls openTxt, single, links, pass, certs := parsed }

/-- The number of lists (open, single term, core link) that contain cell `idx`. -/
def kindsOfS (cd : ChunkDataS) (idx : Nat) : Nat :=
  (if cd.opens.contains idx then 1 else 0) + (if (cd.single.getD idx none).isSome then 1 else 0) +
    (if (cd.links.getD idx none).isSome then 1 else 0)

/-- The claim of a cell checked on one cell of the search (argmin part and rows): `true` if it holds. -/
def claimHolds (cd : ChunkDataS) (idx : Nat) (P : Pair) (ez ew : ETree) (rows : Array Row) : Bool :=
  match cd.single.getD idx none, cd.links.getD idx none with
  | some (nm, lab), _ => checkSingleS P rows nm lab
  | none, some lk =>
    match cd.certs.lookup lk.cert, L6.F34.interiorPoint rows P.nv with
    | some cert, some pt =>
      checkLinkS { P, ez, ew, vars := lk.vars.map (readVar ez ew) } rows pt lk cert
    | _, _ => false
  | none, none => false

/-- The kind of cell `idx` if it passes (`1` single term, `2` core of the first pass, `3` of the second, `4` open; `0`
if it fails), given the cells of the search below its pair (`entries`). Every cell of the search with the line's
argmin part must satisfy the claim, and there must be at least one. -/
def cellKindS (cd : ChunkDataS) (idx : Nat) (entries : List (String × Array Row)) : Nat :=
  if kindsOfS cd idx != 1 then 0
  else if cd.opens.contains idx then 4
  else
    match keyOfLine (cd.cells.getD idx ""), etreesOfLine (cd.cells.getD idx "") with
    | some (kz, kw, am), some (ez, ew) =>
      let P := pairOfKeys kz kw
      let es := entries.filter (·.1 == am)
      if !es.isEmpty && es.all (fun e => claimHolds cd idx P ez ew e.2) then
        (if (cd.single.getD idx none).isSome then 1 else L6.F34.passKind (cd.pass.getD idx 0))
      else 0
    | _, _ => 0

/-- The tree keys of a line (`none` if it does not parse). -/
def pairKeyOf (line : String) : Option ((List Nat × Option Nat) × (List Nat × Option Nat)) :=
  (keyOfLine line).map fun k => (k.1, k.2.1)

/-- The kinds of the cells `idxs`, computing the cells of the search once for each run of lines with the same pair of
trees (`cache`: the last pair and its cells). -/
def kindsRun (cd : ChunkDataS) :
    List Nat → Option (((List Nat × Option Nat) × (List Nat × Option Nat)) × List (String × Array Row)) → List Nat
  | [], _ => []
  | idx :: rest, cache =>
    match pairKeyOf (cd.cells.getD idx "") with
    | none => 0 :: kindsRun cd rest cache
    | some pk =>
      let entries := match cache with
        | some (pk', es) => if pk' == pk then es else cellsBelowR keepLP cd.D (pairOfKeys pk.1 pk.2)
        | none => cellsBelowR keepLP cd.D (pairOfKeys pk.1 pk.2)
      cellKindS cd idx entries :: kindsRun cd rest (some (pk, entries))

/-- **The checker of a chunk**: the inputs parse, `lo ≤ hi ≤` the number of cells, every cell `lo ≤ idx < hi` passes,
and the numbers of cells of each kind are the given ones. -/
def checkChunkS (cls : Nat) (D : Diag) (cellsTxt singleTxt linksTxt passTxt openTxt : String)
    (certs : List (String × String)) (lo hi : Nat) (expected : L6.F34.Counts) : Bool :=
  match prepareS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs with
  | none => false
  | some cd =>
    let ks := kindsRun cd (List.range' lo (hi - lo)) none
    decide (lo ≤ hi) && decide (hi ≤ cd.ncells) && ks.all (· != 0) && decide (L6.F34.countKinds ks = expected)

end L6.F34S
