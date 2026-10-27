# set pr-release-15067-vendored vs the default set (crossset.py).
# The 7 derived instances lose their `_<module>` suffix in the vendored layout (same declarations, same bodies).
rename TermLiveCert.instDecidableEqCfgKey_termLiveCert -> TermLiveCert.instDecidableEqCfgKey
rename TermLiveCert.instDecidableEqExpr_termLiveCert -> TermLiveCert.instDecidableEqExpr
rename TermLiveCert.instDecidableEqMsg_termLiveCert -> TermLiveCert.instDecidableEqMsg
rename TermLiveCert.instDecidableEqOp_termLiveCert -> TermLiveCert.instDecidableEqOp
rename TermLiveCert.instDecidableEqTVal_termLiveCert -> TermLiveCert.instDecidableEqTVal
rename TermLiveCert.instDecidableEqThKey_termLiveCert -> TermLiveCert.instDecidableEqThKey
rename TermLive.instInhabitedCfg_termLive -> TermLive.instInhabitedCfg
# Decidable's match arms print as the structure instance (core rendering, Init)
rule decide-struct
# a renamed (shorter) name lets one `have inst :=` line fit unwrapped
rule rewrap
