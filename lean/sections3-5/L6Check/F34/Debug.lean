import L6F34.Check

/-! Development runner (not a check): runs the F3/F4 checks of a range of cells of one class from the files of the
package and prints the result; `runDebugWith` takes other files (negative controls). -/

namespace L6.F34

def readOr (p : String) : IO String := do
  if ← System.FilePath.pathExists p then IO.FS.readFile p else pure ""

def runDebugWith (cls diagCls lo hi : Nat) (singlePath linksPath certDir : String) : IO Unit := do
  let n6 ← IO.FS.readFile "data/f1/n6.json"
  let cells ← IO.FS.readFile s!"data/cells/c{cls}.jsonl"
  let single ← readOr singlePath
  let links ← readOr linksPath
  let pass ← readOr s!"data/f34/pass/c{cls}.txt"
  let opens ← IO.FS.readFile "data/cells/open43.tsv"
  let ids := ((lines links).filterMap parseLink).filter (fun lk => lo ≤ lk.cell && lk.cell < hi) |>.map (·.cert)
  let ids := ids.eraseDups
  let mut certs : List (String × String) := []
  for id in ids do
    certs := (id, ← IO.FS.readFile s!"{certDir}/{id}.txt") :: certs
  let hi := min hi (numCells cells)
  let t0 ← IO.monoMsNow
  -- the diagram of `diagCls` is used for the cells of `cls` (equal except in negative controls)
  let links' := if diagCls == cls then links else
    String.intercalate "\n" ((lines links).map fun l => match l.splitOn " " with
      | _ :: rest => String.intercalate " " (toString diagCls :: rest)
      | [] => l)
  let r := explainChunk diagCls n6 cells single links' pass opens certs lo hi
  let t1 ← IO.monoMsNow
  match r with
  | .ok c => IO.println s!"class {cls} cells [{lo},{hi}): {repr c} in {t1 - t0} ms ({ids.length} certificates)"
  | .error e => IO.println s!"class {cls} cells [{lo},{hi}): ERROR {e} ({t1 - t0} ms)"

def runDebug (cls lo hi : Nat) : IO Unit :=
  runDebugWith cls cls lo hi s!"data/f34/single/c{cls}.txt" s!"data/f4/links/c{cls}.txt" "data/f4/certs_txt"

end L6.F34
