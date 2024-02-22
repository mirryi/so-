import Lake
open Lake DSL

package «soþ» where
  -- add package configuration options here

lean_lib «Soþ» where
  -- add library configuration options here

@[default_target]
lean_exe «soþ» where
  root := `Main
