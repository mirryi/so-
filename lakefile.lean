import Lake
open Lake DSL

package «soþ» where

lean_lib «CTL» where
lean_lib «Soþ» where

@[default_target]
lean_exe «soþ» where
  root := `Main
