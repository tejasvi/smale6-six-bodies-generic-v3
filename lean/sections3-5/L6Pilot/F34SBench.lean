import L6F34S.Check
import L6F2.Check

/-! Pilot: F3/F4 on the cells of the specification search, against the counts of `per_class.tsv` (development). -/

namespace L6.Pilot

open L6.F34S L6.F2S L6.Poly

/-- The certificate texts named by the links of a class (from `certDir`). -/
def certsOfLinks (linksTxt certDir : String) : IO (List (String × String)) := do
  let ids := ((L6.F34.lines linksTxt).filterMap fun l => (L6.F34.parseLink l).map (·.cert)).eraseDups
  ids.mapM fun id => do
    let t ← IO.FS.readFile s!"{certDir}/{id}.txt"
    return (id, t)

/-- Why cell `idx` fails (or its kind). -/
def explainCell (cd : ChunkDataS) (idx : Nat) (entries : List (String × Array Row)) : String :=
  match keyOfLine (cd.cells.getD idx ""), etreesOfLine (cd.cells.getD idx "") with
  | some (kz, kw, am), some (ez, ew) =>
    let P := pairOfKeys kz kw
    let es := entries.filter (·.1 == am)
    if es.isEmpty then s!"no cell of the search with this argmin part ({entries.length} below the pair)" else
    match cd.single.getD idx none, cd.links.getD idx none with
    | some (nm, lab), _ =>
      let bad := es.filter fun e => !checkSingleS P e.2 nm lab
      s!"single {repr nm} {repr lab}: {bad.length} of {es.length} entries fail"
    | none, some lk =>
      match cd.certs.lookup lk.cert with
      | none => s!"certificate {lk.cert} missing"
      | some cert =>
        let e := es.head!
        match L6.F34.interiorPoint e.2 P.nv with
        | none => "no interior point"
        | some pt =>
          let x : PCtx := { P, ez, ew, vars := lk.vars.map (readVar ez ew) }
          let hdr := cert.nvar == lk.vars.size && cert.fixed == lk.fixed && cert.gens.length == lk.names.size
          let fails := (List.range lk.names.size).filter fun i =>
            genForS x e.2 pt lk.fixed lk.names[i]! != some (normalize cert.gens[i]!)
          let detail := fails.map fun i =>
            let nm := lk.names[i]!
            let what := match L6.F34.IdName.parse nm with
              | some (.dist _ _) => "dist"
              | some n => match XId.ofName n with
                | some I =>
                  let fs := I.terms.map (termForm P)
                  let S := guessArgminS pt fs
                  s!"S={S} const={constantArgminS P.nv e.2 fs S} poly?={(itemPoly x I S lk.fixed).isSome}"
                | none => "no XId"
              | none => "unparsed"
            s!"{nm}: {what}"
          s!"link hdr={hdr} vars={lk.vars.toList} read={(lk.vars.map (readVar ez ew)).toList.map repr} fails={detail}"
    | none, none => "in no list"
  | _, _ => "line does not parse"

/-- Runs the checks of class `k` on the cells `lo ≤ idx < hi` and prints the counts and the first failures. -/
def f34sClass (k lo hi : Nat) (certDir : String) (maxFail : Nat := 5) : IO Unit := do
  let cellsTxt ← IO.FS.readFile s!"data/cells/c{k}.jsonl"
  let single ← IO.FS.readFile s!"data/f34/single/c{k}.txt"
  let links ← IO.FS.readFile s!"data/f4/links/c{k}.txt"
  let pass ← IO.FS.readFile s!"data/f34/pass/c{k}.txt"
  let opn ← IO.FS.readFile "data/cells/open43.tsv"
  let certs ← certsOfLinks links certDir
  let D := L6.F2.diagOf k
  let t0 ← IO.monoMsNow
  match prepareS k D cellsTxt single links pass opn certs with
  | none => IO.println s!"class {k}: inputs do not parse"
  | some cd =>
    let hi := min hi cd.ncells
    let idxs := List.range' lo (hi - lo)
    let ks := kindsRun cd idxs none
    let t1 ← IO.monoMsNow
    let cnt := L6.F34.countKinds ks
    let nfail := (ks.filter (· == 0)).length
    IO.println s!"class {k} [{lo},{hi}): {repr cnt}, failures {nfail}, {t1 - t0} ms"
    let mut shown := 0
    for (idx, kd) in idxs.zip ks do
      if kd == 0 && shown < maxFail then
        shown := shown + 1
        let some pk := pairKeyOf (cd.cells.getD idx "") | IO.println s!"  cell {idx}: no key"
        let entries := cellsBelowR keepLP cd.D (pairOfKeys pk.1 pk.2)
        IO.println s!"  cell {idx}: {explainCell cd idx entries}"

end L6.Pilot
