import Lake
open Lake DSL

package plugin_smoke where
  version := v!"0.1.0"

lean_lib NativePlugin where
  roots := #[`PluginSmoke.NativePlugin]

lean_lib DynamicPayload where
  roots := #[`PluginSmoke.DynamicPayload]

@[default_target]
lean_lib Consumer where
  roots := #[`PluginSmoke.Consumer]
  dynlibs := #[`+PluginSmoke.DynamicPayload:dynlib]
  plugins := #[`+PluginSmoke.NativePlugin:dynlib]
