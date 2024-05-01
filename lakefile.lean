import Lake
open System Lake DSL


package Clingo {
  moreLinkArgs := #["-L.lake/build/lib", "-lclingo-shim", "-lclingo"]
  extraDepTargets := #["clingo-shim"]
}


lean_lib Clingo {
}

def cDir := "bindings"
def ffiSrc := "clingo-shim.c"
def ffiO := "clingo-shim.o"
def ffiLib := "clingo-shim"

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / ffiO
  let srcJob <- inputFile <| pkg.dir / cDir / ffiSrc
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #["-I", (<- getLeanIncludeDir).toString, "-I./",  "-fPIC"]
    compileO ffiSrc oFile srcFile flags

target «clingo-shim» pkg : FilePath := do
   let name := nameToStaticLib ffiLib
   let ffiO <- fetch <| pkg.target ``ffi.o
   buildStaticLib (pkg.buildDir / "lib" / name) #[ffiO]

@[default_target]
lean_exe test_ffi {
  root := `test.TestFFI
}
   
@[default_target]
lean_exe test_lang {
  root := `test.TestLang
}
    
