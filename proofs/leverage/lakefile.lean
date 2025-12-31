import Lake
open Lake DSL

package «leverage» {
  -- add package configuration options here
}

lean_lib «Leverage» {
  -- add library configuration options here
}

@[default_target]
lean_exe «leverage» {
  root := `Main
}
