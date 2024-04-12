import Lake
open Lake DSL

package «soþ» where

lean_lib «TS»  where
lean_lib «CTL» where
lean_lib «Soþ» where

@[default_target]
lean_exe «soþ» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
