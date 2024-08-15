import Lake
open Lake DSL

package «orderedtree» where
  -- add package configuration options here

lean_lib «Orderedtree» where
  -- add library configuration options here

@[default_target]
lean_exe «orderedtree» where
  root := `Main
