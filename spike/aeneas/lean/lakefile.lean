import Lake
open Lake DSL

require aeneas from "../../../../tools/aeneas/aeneas-bin/backends/lean"

package «leb128» where

@[default_target] lean_lib «Leb128» {}
@[default_target] lean_lib «Leb128Proofs» {}
@[default_target] lean_lib «Leb128Spec» {}
@[default_target] lean_lib «Fnv» {}
@[default_target] lean_lib «FnvSpec» {}
