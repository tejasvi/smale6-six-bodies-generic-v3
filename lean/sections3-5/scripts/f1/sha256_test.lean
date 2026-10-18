import L6Common.SHA256

/-! Prints `digest  file` for each file given on the command line, like `sha256sum`, using `L6.SHA256`. -/

def main (args : List String) : IO Unit := do
  for f in args do
    let b ← IO.FS.readBinFile f
    IO.println s!"{L6.SHA256.sha256HexBytes b}  {f}"
