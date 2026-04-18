src/auto_int_plugin_MLPACK_DEPENDENCIES:=src/auto_int_main src/g_auto_int
src/auto_int_main.cmx : FOR_PACK=-for-pack Auto_int_plugin
src/g_auto_int.cmx : FOR_PACK=-for-pack Auto_int_plugin
src/auto_int_plugin.cmo:$(addsuffix .cmo,$(src/auto_int_plugin_MLPACK_DEPENDENCIES))
src/auto_int_plugin.cmx:$(addsuffix .cmx,$(src/auto_int_plugin_MLPACK_DEPENDENCIES))
