import Kraken.X64.Examples.Sbr.SessionBin.WitImage
import Kraken.X64.Examples.Sbr.SessionBin.WitLeafBasic
import Kraken.X64.Examples.Sbr.SessionBin.WitLeafBands
import Kraken.X64.Examples.Sbr.SessionBin.WitLeafMallocz
import Kraken.X64.Examples.Sbr.SessionBin.WitLeafSbrDsp
import Kraken.X64.Examples.Sbr.Parse.VlcWit

/-!
# The witness environment meets the session's contracts

Under the ambient code `wCE` (the image `img` of `WitEnvDefs`), the stand-ins meet the external
contracts at the caller's environment `wEnv`, with init's state `wX`:

* `wInitExt : InitExt wS wX`, the contracts of `ff_aac_sbr_ctx_alloc_init`'s callees;
* `wEnvOK : EnvOK wS wEnv`, the contracts the element's environment meets in a session;
* `wStackBound : StackBound wS`.

And the success outcomes of init's allocations are reachable (`wit_init_success`'s
ingredients):

* `wMalloczOk`: from the heap before the first allocation (`wHeapPtr` holds `wHeapStart`, the
  bytes `[wHeapStart, wHeapEnd)` free), `av_mallocz(n)` with `n ≤ 0x100000` returns the non-null
  `wHeapStart`, holding `n` zero bytes, and leaves a state of `wX`;
* `wTxInitOk`: `av_tx_init` returns `0` and hands out `tx_stub` with an empty context.
-/

open Kraken Kraken.X64.Parser Kraken.SysV Std.WP Mem MachineWP
open Kraken.Examples.Sbr

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.WitEnv

attribute [local instance] wLayout wCE

/-- **Init's external contracts** hold of the stand-ins, with init's state `wX`. -/
theorem wInitExt : SessionBin.InitExt wS wX where
  kle := by decide
  init :=
    { mallocz := mallocz_spec _ pl_mallocz
      txInit := txInit_spec _ _ _ pl_txInit pl_txFn
      psdsp := psdsp_spec _ _ pl_psdsp
      sbrdsp := sbrdsp_spec _ _ pl_sbrdsp }
  psApply := psApply_spec _ _ pl_psApply
  avLog := avLog_spec _ _ pl_avLog
  memcpyV := memcpy_spec _ pl_memcpy
  memsetV := memset_spec _ pl_memset
  avReq := avReq_spec _ _ pl_avReq
  powf := powf_spec _ _ _ pl_powf
  log2f := log2f_spec _ _ _ pl_log2f
  bands := bandsOK_const
  fdsp := ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

/-- The `sbrdsp` slots of `wEnv` are the binary's routines. -/
theorem wSlotsEnv : SbrSlots wEnv :=
  ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

/-- **The element's environment** `wEnv` meets the session's contracts. -/
theorem wEnvOK : SessionBin.EnvOK wS wEnv :=
  ⟨{ psApply := psApply_spec _ _ pl_psApply
     txAna := txFn_spec _ _ _ pl_txFn
     txSyn := txFn_spec _ _ _ pl_txFn
     avLog := avLog_spec _ _ pl_avLog
     memcpyV := memcpy_spec _ pl_memcpy
     memsetV := memset_spec _ pl_memset
     avReq := avReq_spec _ _ pl_avReq
     powf := powf_spec _ _ _ pl_powf
     log2f := log2f_spec _ _ _ pl_log2f
     bands := bandsOK_const
     vlcS := VlcWit.vlcC_sbr wSbrTab
     vlcP := VlcWit.vlcC_ps wPsTab }, wSlotsEnv⟩

/-- The stack bound of `wS`. -/
theorem wStackBound : SessionBin.StackBound wS := by decide

/-- **`av_mallocz` succeeds** on its first call: from the heap before the first allocation
(`wHeapPtr` holds `wHeapStart`, the bytes `[wHeapStart, wHeapEnd)` free, here as `wXAt
wHeapStart`, see `wXAt_start`), a request of `n ≤ 0x100000` bytes returns `wHeapStart ≠ 0`,
holding `n` zero bytes, and leaves a state of `wX` (`AvMalloczSpec wX`'s success disjunct). -/
theorem wMalloczOk (need : Nat) :
    cenv.ProcSpec (entry "av_mallocz")
      (fun (R : Mem 64 → Prop) ra t => (arg0 t).toNat ≤ 0x100000
        ∧ CallPre need (wXAt wHeapStart ⋆ R) ra t)
      (fun R ra t s => s.regs.get64 .rax = wHeapStart ∧ wHeapStart ≠ 0#64
        ∧ CallPost need ((Session.zs (arg0 t).toNat =@ wHeapStart ⋆ wX) ⋆ R) ra t s) := by
  intro R ra t ⟨hn, hpre⟩
  have h1 : isAligned 32 wHeapStart = true := by decide
  have h2 : wHeapStart.toNat ≤ wHeapEnd.toNat := by decide
  have h3 : wHeapStart ≠ 0#64 := by decide
  have h4 : (arg0 t).toNat ≤ (wHeapEnd - wHeapStart).toNat := Nat.le_trans hn (by decide)
  exact eventually_weaken _ _ _ _ (fun st hst => ⟨hst.1, hst.2.1, h3, hst.2.2⟩)
    (mallocz_ok need pl_mallocz (R, wHeapStart) ra t ⟨h1, h2, h3, h4, hpre⟩)

/-- **`av_tx_init` succeeds**: it returns `0` (so `eax ≥ 0`), writing the context `0` (owned as
`emp`, `wEnv.Ctx`) to `*ctx` and the transform `tx_stub` (meeting `TxSpec`) to `*tx`. -/
theorem wTxInitOk (TxTab X : Mem 64 → Prop) (need : Nat) :
    cenv.ProcSpec (entry "av_tx_init")
      (fun (R : Mem 64 → Prop) ra t =>
        CallPre need ((8 ?@ arg0 t ⋆ (8 ?@ arg1 t ⋆ Init.TxIn TxTab X t)) ⋆ R) ra t)
      (fun R ra t s => s.regs.get64 .rax = 0#64
        ∧ CallPost need ((TxOkF TxTab X t) ⋆ R) ra t s) := by
  have hpl := pl_txInit
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := txInitT) (txOkTable TxTab X need)
    (Post' (fun _ s => s.regs.get64 .rax = 0#64) (TxOkF TxTab X) need) (hblocks := ?_)
    (hpre := fun _ _ _ h => ⟨rfl, pre_of_call (F := TxInF TxTab X) h⟩)
    (hpost := fun _ _ _ _ h => (post_of_ret h).symm)
  intro R ra t₀
  cfg_cases [txInitT]
  · vcgen
    all_goals (try simp only [txOkTable.match_1.eq_1] at *)
    all_goals (try obtain ⟨⟨rfl, _⟩, _⟩ := ‹_ ∧ _›)
    all_goals grind_cells
  · vcgen
    all_goals grind_cells
  · leaf_block

end Kraken.Examples.Sbr.WitEnv
