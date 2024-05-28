import Lake
open Lake DSL

package «FMCn» where
  -- add package configuration options here

lean_lib «FMCn» where
  -- add library configuration options here

@[default_target]
lean_exe «fmcn» where
  root := `Main
