import L6K.F2S.SearchRL
import L6K.F2S.Keep
import L6K.F34K.Check
import L6F34S.Check
import L6F34.Point
import L6F2.Check
import Std.Data.HashMap

/-!
# Exporter of the kernel run of F2–F4 (compiled code, untrusted)

For one class and a range of its pairs of partial trees after `d` insertions, runs the search with the rows of each
cell (`belowRL`) natively, with the decisions of `keepLP`, and cuts each subtree into *units* of at most `B` programs:
a node whose subtree has at most `B` programs (or a complete pair) is a unit; a larger node is expanded one level (a
*level node*). For each unit it writes the certificate table of its discarded programs (`C hash i:y …`, entries in
increasing order of row index) and the claims of its cells, in the order of the search, as Lean source
(`L6K.F34K.ClaimK`: the identity and term of a single-term cell with the certificates of its linear programs, or the
certificate index, fixed mass, variables, engine trees and items of a core cell, each item with its argmin set and the
certificates of its constancy). For each level node it writes the table of its level and its children.

Small siblings are put together into one unit (consecutive, at most `B` programs in all). Output, under
`OUT/c<c>/`: `n<id>.tbl`, `n<id>.claims` and one line per node in `nodes_<i0>_<i1>.txt`:
`U id depth programs P cells N nodes S tz-nodes / tz-leafO / tw-nodes / tw-leafO ; …` for a unit (its sibling
nodes), `L id depth S tz… / tw… programs P children id id …` for a level node (`-` for an absent leaf body), and
`R pair id` for the root of each pair of the range. The unit budget is on a weight: three per program of the tree
levels, one per program of the argmin stage. In the prefix mode the first `d` insertions are written as level nodes
whose children at depth `d` are `P<k>`, the pair `k` of `prefixPairsL` (file `nodes_prefix.txt`, `R prefix id`).
-/

namespace L6K.F34K.Export

open L6 L6.F2S L6.F34S L6.Poly L6K.F2S
open L6.F34 (Lab IdName Link)
open L6.F2 (Diag renderEntry)

/-! ## The decisions, recorded -/

initialize cntRef : IO.Ref Nat ← IO.mkRef 0
initialize logRef : IO.Ref (Array (Nat × List (Nat × Int))) ← IO.mkRef #[]
initialize badRef : IO.Ref Nat ← IO.mkRef 0

/-- A certificate with its entries in increasing order of row index (`none` if an index repeats). -/
def sortCert (c : List (Nat × Int)) : Option (List (Nat × Int)) :=
  let s := (c.filter (·.2 != 0)).mergeSort fun a b => a.1 ≤ b.1
  if (s.zip (s.drop 1)).all fun ab => ab.1.1 < ab.2.1 then some s else none

/-- `keepLP`, counting the programs and recording the certificate of each discarded one under its hash. -/
unsafe def keepRecImpl (rows : List Row) (nv : Nat) : Bool :=
  let arr := rows.toArray
  let v := LP.decide arr nv
  -- depends on the program, so that the compiler does not evaluate it once for all calls
  let c := unsafeBaseIO (do cntRef.modify (· + (if rows.length == 0 then 2 else 1)); return (← cntRef.get))
  if c != 0 && !v.kept && Farkas.check nv arr v.cert then
    match sortCert v.cert with
    | some s =>
      let n := unsafeBaseIO (do logRef.modify (·.push (rowsHash arr, s)); return (← logRef.get).size)
      n == 0
    | none =>
      let n := unsafeBaseIO (do badRef.modify (· + 1); return (← badRef.get))
      n == 0
  else true

@[implemented_by keepRecImpl] opaque keepRec : List Row → Nat → Bool

/-- The certificate of the program `rows + {r}` (`r` last), its entries sorted; `none` if `keepLP` keeps it. -/
def lpCert (nv : Nat) (rows : List Row) (r : Row) : Option (List (Nat × Int)) :=
  let rs := (rows ++ [r]).toArray
  let v := LP.decide rs nv
  if !v.kept && Farkas.check nv rs v.cert then sortCert v.cert else none

/-! ## Lean source -/

def boolS (b : Bool) : String := if b then "true" else "false"
def natsS (l : List Nat) : String := "[" ++ ", ".intercalate (l.map toString) ++ "]"
def certS (c : List (Nat × Int)) : String := "[" ++ ", ".intercalate (c.map fun (i, y) => s!"({i}, {y})") ++ "]"
def certsS (cs : List (List (Nat × Int))) : String := "[" ++ ", ".intercalate (cs.map certS) ++ "]"

def idNameS : IdName → String
  | .body z k => s!"(.body {boolS z} {k})"
  | .U => ".U"
  | .I => ".I"
  | .dist k l => s!"(.dist {k} {l})"
  | .torque J => s!"(.torque {natsS J})"
  | .virial J => s!"(.virial {natsS J})"
  | .diff z k l => s!"(.diff {boolS z} {k} {l})"
  | .subset z J => s!"(.subset {boolS z} {natsS J})"
  | .Ip => ".Ip"
  | .UI => ".UI"

def labS : Lab → String
  | .pos i => s!"(.pos {i})"
  | .cross i j => s!"(.cross {i} {j})"
  | .delta k l => s!"(.delta {k} {l})"
  | .zw k l => s!"(.zw {k} {l})"
  | .E => ".E"
  | .zkwk k => s!"(.zkwk {k})"
  | .T1 k l => s!"(.T1 {k} {l})"
  | .T2 k l => s!"(.T2 {k} {l})"
  | .V0 k => s!"(.V0 {k})"
  | .V1 k l => s!"(.V1 {k} {l})"
  | .V2 k l => s!"(.V2 {k} {l})"
  | .V3 k l => s!"(.V3 {k} {l})"
  | .D0 z a b => s!"(.D0 {boolS z} {a} {b})"
  | .D1 z a b => s!"(.D1 {boolS z} {a} {b})"
  | .D2 z a b => s!"(.D2 {boolS z} {a} {b})"
  | .SP z i => s!"(.SP {boolS z} {i})"
  | .SC z i j => s!"(.SC {boolS z} {i} {j})"
  | .E0 => ".E0"
  | .U k l => s!"(.U {k} {l})"
  | .Ip k => s!"(.Ip {k})"

def varS : VarM → String
  | .X v c c0 => s!"(.X {v} {c} {c0})"
  | .Y v c c0 => s!"(.Y {v} {c} {c0})"
  | .D k l => s!"(.D {k} {l})"
  | .E => ".E"
  | .bad => ".bad"

def etreeS (t : ETree) : String :=
  "[" ++ ", ".intercalate (t.map fun (v, m, cs) => s!"({v}, {m}, {natsS cs})") ++ "]"

def itemS (it : ItemK) : String := s!"⟨{idNameS it.nm}, {natsS it.S}, {certsS it.cA}, {certsS it.cB}⟩"

def claimS : ClaimK → String
  | .single nm lab cs => s!"(.single {idNameS nm} {labS lab} {certsS cs})"
  | .core j f vars ez ew items =>
    s!"(.core {j} ({f}) #[" ++ ", ".intercalate (vars.toList.map varS) ++ s!"] {etreeS ez} {etreeS ew} [" ++
      ", ".intercalate (items.map itemS) ++ "])"

def tsS (t : TS) : String :=
  " ".intercalate (t.nodes.map toString) ++ " / " ++ (match t.leafO with | some k => toString k | none => "-")

/-! ## The claim of a cell -/

/-- The certificates of the programs `rows + {row k}` for the terms `k` (empty where no program is needed). -/
def certsFor (nv : Nat) (rows : List Row) (n : Nat) (rowOf : Nat → Option Row) : Except String (List (List (Nat × Int))) :=
  (List.range n).mapM fun k =>
    match rowOf k with
    | none => pure []
    | some r => match lpCert nv rows r with
      | some c => pure c
      | none => throw s!"no certificate for term {k}"

/-- The claim of the stored cell `idx` at the pair `P` with the rows `rows`. -/
def claimOf (cd : ChunkDataS) (idx : Nat) (P : Pair) (rows : List Row) (certIdx : String → Option Nat) :
    Except String ClaimK := do
  match cd.single.getD idx none, cd.links.getD idx none with
  | some (nm, lab), _ =>
    let some I := XId.ofName nm | throw "unknown identity"
    let fs := I.terms.map (termForm P)
    let some i := findLabX I.terms lab | throw "unknown term"
    let some fi := fs.getD i none | throw "term with exponent ⊤"
    let cs ← certsFor P.nv rows fs.length fun k =>
      if k == i then none else (fs.getD k none).map fun fk => rowLe fk fi
    pure (.single nm lab cs)
  | none, some lk =>
    let some (ez, ew) := etreesOfLine (cd.cells.getD idx "") | throw "engine trees"
    let vars := lk.vars.map (readVar ez ew)
    let some pt := L6.F34.interiorPoint rows.toArray P.nv | throw "interior point"
    let items ← lk.names.toList.mapM fun nmS => do
      let some nm := L6.F34.IdName.parse nmS | throw s!"name {nmS}"
      match nm with
      | .dist _ _ => pure (⟨nm, [], [], []⟩ : ItemK)
      | _ =>
        let some I := XId.ofName nm | throw "unknown identity"
        let fs := I.terms.map (termForm P)
        let S := guessArgminS pt fs
        let some i0 := S.head? | throw "empty argmin set"
        let some f0 := fs.getD i0 none | throw "argmin with exponent ⊤"
        let cA ← certsFor P.nv rows fs.length fun k =>
          if k == i0 then none else (fs.getD k none).map fun fk =>
            if S.contains k then rowGeS fk f0 else rowLe fk f0
        let cB ← certsFor P.nv rows fs.length fun k =>
          if k == i0 || !S.contains k then none else (fs.getD k none).map fun fk => rowGeS f0 fk
        pure ⟨nm, S, cA, cB⟩
    let some j := certIdx lk.cert | throw s!"certificate {lk.cert}"
    pure (.core j lk.fixed vars ez ew items)
  | none, none => throw s!"cell {idx} has no claim"

/-- The argmin string of a cell of the search (the stored form), from the identities of its pair. -/
def argminStr (ids : List SIdent) (es : List (Nat × List Nat)) : String :=
  ", ".intercalate (es.map fun e =>
    let id := ids.getD e.1 default
    renderEntry id.name (e.2.map fun t => id.labels.getD t .E).toArray)

/-! ## The walk -/

/-- The data of a subtree: programs, certificates, claims (as source), number of cells. -/
structure Sub where
  programs : Nat
  /-- The cost estimate: three per program of the tree levels, one per program of the argmin stage. -/
  weight : Nat
  certs : Array (Nat × List (Nat × Int))
  claims : Array String
  deriving Inhabited

structure Ctx where
  D : Diag
  cd : ChunkDataS
  stored : Std.HashMap (((List Nat × Option Nat) × (List Nat × Option Nat)) × String) Nat
  certIdx : String → Option Nat
  budget : Nat
  out : String

initialize nodeRef : IO.Ref Nat ← IO.mkRef 0
initialize linesRef : IO.Ref (Array String) ← IO.mkRef #[]

def newId : IO Nat := do
  let n ← nodeRef.get
  nodeRef.set (n + 1)
  return n

def certLines (log : Array (Nat × List (Nat × Int))) : List String :=
  (log.toList.mergeSort fun a b => a.1 ≤ b.1).map fun (h, c) =>
    "C " ++ toString h ++ " " ++ " ".intercalate (c.map fun (i, y) => s!"{i}:{y}")

/-- Writes a unit: consecutive sibling nodes `(S, tz, tw)` at depth `depth` with the data of their subtrees. -/
def writeUnit (cx : Ctx) (depth : Nat) (nodes : List (Nat × TS × TS)) (s : Sub) : IO Nat := do
  let id ← newId
  IO.FS.writeFile s!"{cx.out}/n{id}.tbl" ("\n".intercalate (certLines s.certs) ++ "\n")
  IO.FS.writeFile s!"{cx.out}/n{id}.claims" ("[" ++ ",\n  ".intercalate s.claims.toList ++ "]\n")
  linesRef.modify (·.push (s!"U {id} {depth} programs {s.programs} weight {s.weight} cells {s.claims.size} nodes " ++
    " ; ".intercalate (nodes.map fun x => s!"{x.1} {tsS x.2.1} / {tsS x.2.2}")))
  return id

/-- The cells below a complete pair: programs, certificates, claims. -/
def leafSub (cx : Ctx) (tz tw : TS) : IO Sub := do
  cntRef.set 0
  logRef.set #[]
  let P : Pair := ⟨tz, tw⟩
  let cells := cellsBelowRL keepRec cx.D P
  let n ← cntRef.get
  let log ← logRef.get
  let ids := (idents cx.D P).getD []
  let mut claims : Array String := #[]
  for (am, rows) in cells do
    let key := ((tz.key, tw.key), argminStr ids am)
    match cx.stored.get? key with
    | none => throw (IO.userError s!"cell not stored: {key.2}")
    | some idx =>
      match claimOf cx.cd idx P rows cx.certIdx with
      | .ok c => claims := claims.push (claimS c)
      | .error e => throw (IO.userError s!"cell {idx}: {e}")
  return ⟨n, n, log, claims⟩

/-- The walk below the node `(S, tz, tw)` at depth `depth` with the remaining bodies `rest`: `inl sub` if the subtree
is small (at most the budget, not yet written), `inr id` if it was written (unit or level node). -/
partial def walk (cx : Ctx) (depth : Nat) (rest : List Nat) (S : Nat) (tz tw : TS) : IO (Sub ⊕ Nat) := do
  match rest with
  | [] =>
    let s ← leafSub cx tz tw
    if s.weight ≤ cx.budget then return .inl s else return .inr (← writeUnit cx depth [(S, tz, tw)] s)
  | p :: rest' =>
    let S' := ins p S
    -- the level: the programs of the options, the kept children
    cntRef.set 0
    logRef.set #[]
    let mut kids : Array (TS × TS) := #[]
    for tz' in tz.options S p do
      for tw' in tw.options S p do
        match partialRowsL cx.D ⟨tz', tw'⟩ S' with
        | none => pure ()
        | some L => if keepRec L (Pair.nv ⟨tz', tw'⟩) then kids := kids.push (tz', tw')
    let levelN ← cntRef.get
    let levelLog ← logRef.get
    let mut results : Array (Sub ⊕ Nat) := #[]
    for (tz', tw') in kids do
      results := results.push (← walk cx (depth + 1) rest' S' tz' tw')
    let allSmall := results.all fun r => match r with | .inl _ => true | .inr _ => false
    let total := 3 * levelN + results.foldl (fun acc r => acc + match r with | .inl s => s.weight | .inr _ => 0) 0
    if allSmall && total ≤ cx.budget then
      let merged := results.foldl (fun (acc : Sub) r => match r with
        | .inl s => ⟨acc.programs + s.programs, acc.weight + s.weight, acc.certs ++ s.certs, acc.claims ++ s.claims⟩
        | .inr _ => acc) ⟨levelN, 3 * levelN, levelLog, #[]⟩
      return .inl merged
    else
      -- the small children in batches of consecutive siblings of at most the budget, then this node as a level node
      let mut kidIds : Array Nat := #[]
      let mut batch : Array (Nat × TS × TS) := #[]
      let mut bsub : Sub := ⟨0, 0, #[], #[]⟩
      for (kid, r) in kids.zip results do
        match r with
        | Sum.inl s =>
          if batch.size > 0 && bsub.weight + s.weight > cx.budget then
            kidIds := kidIds.push (← writeUnit cx (depth + 1) batch.toList bsub)
            batch := #[]
            bsub := ⟨0, 0, #[], #[]⟩
          batch := batch.push (S', kid.1, kid.2)
          bsub := ⟨bsub.programs + s.programs, bsub.weight + s.weight, bsub.certs ++ s.certs, bsub.claims ++ s.claims⟩
        | Sum.inr id =>
          if batch.size > 0 then
            kidIds := kidIds.push (← writeUnit cx (depth + 1) batch.toList bsub)
            batch := #[]
            bsub := ⟨0, 0, #[], #[]⟩
          kidIds := kidIds.push id
      if batch.size > 0 then
        kidIds := kidIds.push (← writeUnit cx (depth + 1) batch.toList bsub)
      let id ← newId
      IO.FS.writeFile s!"{cx.out}/n{id}.tbl" ("\n".intercalate (certLines levelLog) ++ "\n")
      linesRef.modify (·.push (s!"L {id} {depth} {S} {tsS tz} / {tsS tw} programs {levelN} children " ++
        " ".intercalate (kidIds.toList.map toString)))
      return .inr id

/-- The prefix of the search (the first `dStop` insertions), as level nodes; the pairs after `dStop` insertions are
referred to as `P<k>`, `k` their position in `prefixPairsL`. -/
partial def walkPrefix (cx : Ctx) (depth dStop : Nat) (rest : List Nat) (S : Nat) (tz tw : TS) (ctr : IO.Ref Nat) :
    IO String := do
  if depth == dStop then
    let k ← ctr.get
    ctr.set (k + 1)
    return s!"P{k}"
  match rest with
  | [] => throw (IO.userError "prefix deeper than the insertions")
  | p :: rest' =>
    let S' := ins p S
    cntRef.set 0
    logRef.set #[]
    let mut kids : Array (TS × TS) := #[]
    for tz' in tz.options S p do
      for tw' in tw.options S p do
        match partialRowsL cx.D ⟨tz', tw'⟩ S' with
        | none => pure ()
        | some L => if keepRec L (Pair.nv ⟨tz', tw'⟩) then kids := kids.push (tz', tw')
    let levelN ← cntRef.get
    let levelLog ← logRef.get
    let mut refs : Array String := #[]
    for (tz', tw') in kids do
      refs := refs.push (← walkPrefix cx (depth + 1) dStop rest' S' tz' tw' ctr)
    let id ← newId
    IO.FS.writeFile s!"{cx.out}/n{id}.tbl" ("\n".intercalate (certLines levelLog) ++ "\n")
    linesRef.modify (·.push (s!"L {id} {depth} {S} {tsS tz} / {tsS tw} programs {levelN} children " ++
      " ".intercalate refs.toList))
    return toString id

/-- The context of class `c` (data of the lean6 tree `dir`), with output under `out/c<c>`. -/
def loadCtx (c b : Nat) (dir out : String) : IO (Ctx × List Nat) := do
  let D := L6.F2.diagOf c
  let ord := order D
  let dg := L6.F2.classes6[c]!
  IO.println s!"class {c} diagram {dg.e} {dg.zc} {dg.wc} order {",".intercalate (ord.map toString)}"
  let readOr (p : String) : IO String := do
    if ← System.FilePath.pathExists p then IO.FS.readFile p else pure ""
  let cells ← readOr s!"{dir}/data/cells/c{c}.jsonl"
  let single ← readOr s!"{dir}/data/f34/single/c{c}.txt"
  let links ← readOr s!"{dir}/data/f4/links/c{c}.txt"
  let pass ← readOr s!"{dir}/data/f34/pass/c{c}.txt"
  let openTxt ← readOr s!"{dir}/data/cells/open43.tsv"
  let some cd := prepareS c D cells single links pass openTxt [] | throw (IO.userError "prepare")
  let mut stored : Std.HashMap (((List Nat × Option Nat) × (List Nat × Option Nat)) × String) Nat := {}
  for idx in [0:cd.ncells] do
    match keyOfLine (cd.cells.getD idx "") with
    | some (kz, kw, am) => stored := stored.insert ((kz, kw), am) idx
    | none => pure ()
  let certNames := ((← System.FilePath.readDir s!"{dir}/data/f4/certs_txt").toList.map
    (fun e => e.fileName.replace ".txt" "")).mergeSort (· ≤ ·)
  let certMap : Std.HashMap String Nat := (certNames.zipIdx).foldl (fun m (s, i) => m.insert s i) {}
  let outDir := s!"{out}/c{c}"
  IO.FS.createDirAll outDir
  return (⟨D, cd, stored, fun s => certMap.get? s, b, outDir⟩, ord)

/-- `c d i0 i1 B DIR OUT`: the pairs `i0 … i1-1` after `d` insertions of class `c` (data of the lean6 tree `DIR`);
`prefix c d DIR OUT`: the prefix of class `c` down to those pairs. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["info"] =>
    for c in [0:191] do
      let dg := L6.F2.classes6[c]!
      IO.println s!"{c} {dg.e} {dg.zc} {dg.wc} {",".intercalate ((order (L6.F2.diagOf c)).map toString)}"
  | ["prefix", c, d, dir, out] =>
    let (cx, ord) ← loadCtx c.toNat! 0 dir out
    nodeRef.set 2000000000
    linesRef.set #[]
    let ctr ← IO.mkRef 0
    let r ← walkPrefix cx 0 d.toNat! ord (single L6.F2S.O) TS.init TS.init ctr
    linesRef.modify (·.push s!"R prefix {r}")
    let h ← IO.FS.Handle.mk s!"{cx.out}/nodes_prefix.txt" .write
    for l in (← linesRef.get) do h.putStrLn l
    h.flush
    IO.println s!"class {c} prefix depth {d} pairs {← ctr.get} bad certificates {← badRef.get}"
  | [c, d, i0, i1, b, dir, out] =>
    let (cx, ord) ← loadCtx c.toNat! b.toNat! dir out
    let d := d.toNat!
    let pre := prefixPairsL (fun r nv => keepLP r.toArray nv) cx.D ord d
    nodeRef.set (i0.toNat! * 1000000)
    linesRef.set #[]
    for i in [i0.toNat!:min i1.toNat! pre.length] do
      let x := pre[i]!
      let r ← walk cx d (ord.drop d) x.1 x.2.1 x.2.2
      let id ← match r with
        | .inl s => writeUnit cx d [x] s
        | .inr id => pure id
      linesRef.modify (·.push s!"R {i} {id}")
    let h ← IO.FS.Handle.mk s!"{cx.out}/nodes_{i0}_{i1}.txt" .write
    for l in (← linesRef.get) do h.putStrLn l
    h.flush
    IO.println s!"class {c} pairs {pre.length} done {i0}..{i1} bad certificates {← badRef.get}"
  | _ => IO.println "usage: f34kexport c d i0 i1 B DIR OUT | f34kexport prefix c d DIR OUT"

end L6K.F34K.Export

def main (args : List String) : IO Unit := L6K.F34K.Export.main args
