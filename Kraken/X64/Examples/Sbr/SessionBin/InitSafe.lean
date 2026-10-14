import Kraken.X64.Examples.Sbr.SessionBin.TopDefs
import Kraken.X64.Examples.Sbr.Parse.InitLink
import Kraken.X64.Examples.Sbr.Parse.InitProc

/-!
# `ff_aac_sbr_ctx_alloc_init`, composed with the session

A call of `ff_aac_sbr_ctx_alloc_init(ac, che, id)` returns; on `0` the element at the address
`p` it stored to `*che` is `Live`, in an environment meeting the session's contracts (the
externals at the caller's environment and the two transforms init set up), with the caller's
`ac` fields back as `AcFields`; otherwise as `InitPost`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-! ## Hypotheses -/

/-- The external contracts at the caller's environment `S.env`, with init's state `X`. -/
structure InitExt (S : Setup) (X : Mem 64 → Prop) : Prop where
  /-- The stack reservation fits in 32 bits. -/
  kle : S.k ≤ 2 ^ 32
  /-- Init's externals (`av_tx_init`, `av_mallocz`, `av_free`, …). -/
  init : InitAssumed S.k S.env.Ctx S.env.TxTab X
  /-- `ff_ps_apply`. -/
  psApply : PsApplySpec S.env.PsTab S.k
  /-- `av_log` on the logging state. -/
  avLog : AvLogSpec S.env.Ext S.k
  /-- `memcpy`, as a value contract. -/
  memcpyV : MemcpyValSpec S.k
  /-- `memset`, as a value contract. -/
  memsetV : MemsetValSpec S.k
  /-- `avpriv_request_sample` on the logging state. -/
  avReq : DecExt.AvReqSpec S.env.Ext S.k
  /-- `powf` computes `S.pw`. -/
  powf : Reset.PowfSpec ⟨S.env.Ext, S.pw, S.lg⟩ S.k
  /-- `log2f` computes `S.lg`. -/
  log2f : Reset.Log2fSpec ⟨S.env.Ext, S.pw, S.lg⟩ S.k
  /-- The floating-point facts on `S.pw`, `S.lg`. -/
  bands : Reset.BandsOK S.lg S.pw
  /-- The `float_dsp` slots of `S.env`. -/
  fdsp : FdspOK S.env

/-- What the caller owns at the call besides `*che` and init's state: the `ac` fields, the
`ac->fdsp` cell, the `float_dsp` slots, the PS tables, `av_log`'s state, the constants, the
parser's static data, and the rest `Rest`. -/
abbrev InitOwn (S : Setup) (ac avctx fdsp : BitVec 64) (er ps : BitVec 32)
    (Rest : Mem 64 → Prop) : Mem 64 → Prop :=
  AcFields ac avctx er ps ⋆ (c8 (ac + 0x2550#64) fdsp ⋆ (FdspW S.env fdsp ⋆ (S.env.PsTab
    ⋆ (S.env.Ext ⋆ (CstW ⋆ (PStat S.vs S.vp ⋆ Rest))))))

/-! ## Transport -/

/-- The session's contracts at the environment init produced: the externals at `S.env` and the
contracts of the two transforms `av_tx_init` returned. -/
theorem envOK_envOf {S : Setup} {X : Mem 64 → Prop} {r : IR} (h : InitExt S X)
    (ha : TxSpec S.env.Ctx S.env.TxTab S.k r.anaFn)
    (hs : TxSpec S.env.Ctx S.env.TxTab S.k r.synFn) (hsl : DspSlotsOK r.sl) :
    EnvOK S (envOf S.env r) :=
  ⟨⟨h.psApply, ha, hs, h.avLog, h.memcpyV, h.memsetV, h.avReq, h.powf, h.log2f, h.bands,
    VlcWit.vlcC_sbr _, VlcWit.vlcC_ps _⟩, sbrSlots_envOf hsl h.fdsp⟩

/-! ## Init's success as a live element -/

omit [CodeEnv] in
theorem initSafe_perm1 (Ch E C1 C2 Tx X Ac Fd Pt Ex Cs Ps Rest : Mem 64 → Prop) :
    ((Ch ⋆ (E ⋆ (C1 ⋆ C2))) ⋆ (Tx ⋆ X)) ⋆ (Ac ⋆ (Fd ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ (Ps ⋆ Rest))))))
    = E ⋆ (C1 ⋆ (C2 ⋆ (Ac ⋆ (Fd ⋆ (Tx ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ (Ps ⋆ (Ch ⋆ (X ⋆ Rest))))))))))) := by
  ac_rfl

omit [CodeEnv] in
theorem initSafe_perm2 (X1 X2 X3 X4 F : Mem 64 → Prop) :
    (X1 ⋆ (X3 ⋆ X4)) ⋆ (X2 ⋆ F) = X1 ⋆ (X2 ⋆ (X3 ⋆ X4)) ⋆ F := by
  ac_rfl

omit [CodeEnv] in
theorem initSafe_perm3 (A B G F : Mem 64 → Prop) : (A ⋆ B) ⋆ (G ⋆ F) = (A ⋆ G) ⋆ (B ⋆ F) := by
  ac_rfl

/-- Init's success memory with the caller's parts is the session memory at init's values. -/
theorem init_sessW_full {e₀ : Env} {r : IR} {id : BitVec 32} {R : Mem 64 → Prop}
    {avctx fdsp : BitVec 64} {extRate ps : BitVec 32} (vs : Nat → Vlc.VlcTab)
    (vp : Nat → Ps.VlcTab) {che : BitVec 64} {X Rest : Mem 64 → Prop} {t : MachineData}
    {m : Mem 64} (hp : arg1 t = r.p) (hpsd : r.psd.length = 64)
    (h : m =⋆ (InitOK e₀.Ctx che id r ⋆ (e₀.TxTab ⋆ X))
      ⋆ (AcW (xInit (inOf r id R avctx fdsp extRate ps)) t ⋆ (FdspW e₀ fdsp ⋆ (e₀.PsTab
      ⋆ (e₀.Ext ⋆ (CstW ⋆ (PStat vs vp ⋆ Rest))))))) :
    m =⋆ SessW (envOf e₀ r) vs vp (σInit (inOf r id R avctx fdsp extRate ps)) t
      ⋆ (InitGap r.p ⋆ (Apply.c8 che r.p ⋆ (X ⋆ Rest))) := by
  unfold InitOK at h
  rw [initSafe_perm1] at h
  exact init_sessW (d := toDS (σInit (inOf r id R avctx fdsp extRate ps))) hp hpsd rfl rfl rfl
    rfl rfl rfl h

/-- Init's success memory with the caller's parts is a live element at `r.p`, `ac`, the caller's
`ac` fields, the cell `*che = r.p`, init's state and the rest. -/
theorem init_live_elem {S : Setup} {r : IR} {id : BitVec 32} {avctx fdsp : BitVec 64}
    {er ps : BitVec 32} {che ac : BitVec 64} {X Rest : Mem 64 → Prop} {m : Mem 64}
    (henv : EnvOK S (envOf S.env r)) (hpsd : r.psd.length = 64)
    (h : m =⋆ (InitOK S.env.Ctx che id r ⋆ (S.env.TxTab ⋆ X))
      ⋆ InitOwn S ac avctx fdsp er ps Rest) :
    m =⋆ Live S r.p ac ⋆ (AcFields ac avctx er ps ⋆ (Apply.c8 che r.p ⋆ (X ⋆ Rest))) := by
  have h' : m =⋆ (InitOK S.env.Ctx che id r ⋆ (S.env.TxTab ⋆ X))
      ⋆ (AcW (xInit (inOf r id Rest avctx fdsp er ps)) (tAt r.p ac) ⋆ (FdspW S.env fdsp
      ⋆ (S.env.PsTab ⋆ (S.env.Ext ⋆ (CstW ⋆ (PStat S.vs S.vp ⋆ Rest)))))) := by
    obtain ⟨a, b, hu, hi, ha, hb⟩ := h
    refine ⟨a, b, hu, hi, ha, ?_⟩
    unfold InitOwn AcFields at hb
    rw [initSafe_perm2] at hb
    simp only [AcW, tAt_arg0]
    exact hb
  have h3 := init_sessW_full S.vs S.vp (tAt_arg1 r.p ac) hpsd h'
  rw [sessW_split, tAt_arg0, tAt_arg1, initSafe_perm3] at h3
  obtain ⟨m1, m2, hu, hi, h4, h5⟩ := h3
  exact ⟨m1, m2, hu, hi, ⟨true, envOf S.env r, _, _, henv, SReach.init, h4⟩, h5⟩

omit [CodeEnv] in
theorem initSafe_sep_r2 {A B P Q : Mem 64 → Prop} (h : ∀ m, P m → Q m) {m : Mem 64}
    (hm : (A ⋆ (B ⋆ P)) m) : (A ⋆ (B ⋆ Q)) m := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, hd⟩ := hm
  exact ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, h d hd⟩

omit [CodeEnv] in
theorem initSafe_sep_imp {P P' Q Q' : Mem 64 → Prop} (hp : ∀ m, P m → P' m)
    (hq : ∀ m, Q m → Q' m) : ∀ m, (P ⋆ Q) m → (P' ⋆ Q') m := by
  rintro m ⟨m1, m2, hu, hd, h1, h2⟩
  exact ⟨m1, m2, hu, hd, hp _ h1, hq _ h2⟩

omit [CodeEnv] in
theorem initSafe_perm4 (C J T R : Mem 64 → Prop) :
    (C ⋆ (J ⋆ T)) ⋆ R = ((C ⋆ T) ⋆ R) ⋆ J := by
  ac_rfl

/-! ## Init, composed -/

/-- What `ff_aac_sbr_ctx_alloc_init(ac, che, id)` (called in `t`, returning to `ra`) leaves in
`s`: on `0`, an address `p` such that the element at `p` (of `ac`) is live, with the caller's
`ac` fields, the cell `*che = p`, init's state `X` and the rest; otherwise a nonzero result and
the caller's objects given back (the 8 bytes at `che`, the transforms' tables, `X`, everything
of `InitOwn`), with some further memory `J` (what init allocated before it failed). -/
def InitQ (S : Setup) (X Rest : Mem 64 → Prop) (avctx fdsp : BitVec 64) (er ps : BitVec 32)
    (ra : Int64) (t s : MachineData) : Prop :=
  (ret32 s = 0#32 ∧ ∃ p : BitVec 64, CallPost (initNeed S.k) (Live S p (arg0 t)
      ⋆ (AcFields (arg0 t) avctx er ps ⋆ (Apply.c8 (arg1 t) p ⋆ (X ⋆ Rest)))) ra t s)
  ∨ (ret32 s ≠ 0#32 ∧ ∃ J : Mem 64 → Prop, CallPost (initNeed S.k)
      (((8 ?@ arg1 t ⋆ (S.env.TxTab ⋆ X)) ⋆ InitOwn S (arg0 t) avctx fdsp er ps Rest) ⋆ J)
      ra t s)

/-- **Init, composed.** A call of `ff_aac_sbr_ctx_alloc_init(ac, che, id)` with the caller's
parts returns to `ra` with `InitQ` (and reaches no stop). -/
theorem init_safe {S : Setup} {X : Mem 64 → Prop} (hpl : Program.PlacedIn Init.body)
    (hx : InitExt S X) {avctx fdsp : BitVec 64} {er ps : BitVec 32} {Rest : Mem 64 → Prop}
    {ra : Int64} {t₀ : MachineData}
    (hpre : InitPre S.k S.env.TxTab X (InitOwn S (arg0 t₀) avctx fdsp er ps Rest) ra t₀) :
    Ends "ff_aac_sbr_ctx_alloc_init" t₀ ra (InitQ S X Rest avctx fdsp er ps ra t₀) NoStops := by
  refine eventually_weaken _ _ _ _ (fun st hs => Or.inl ⟨hs.1, ?_⟩)
    (Init.spec hpl S.k hx.kle _ _ _ hx.init _ ra t₀ hpre)
  rcases hs.2 with ⟨h0, r, hpsd, hsl, hta, hts, h1, h2, h3, hm⟩ | h
  · exact Or.inl ⟨h0, r.p, h1, h2, h3,
      initSafe_sep_r2 (fun m hm' => init_live_elem (envOK_envOf hx hta hts hsl) hpsd hm') hm⟩
  · rcases h with ⟨h0, h1, h2, h3, hm⟩ | ⟨h0, p, J, h1, h2, h3, hm⟩
    · refine Or.inr ⟨by unfold ret32; rw [h0]; decide, Std.ExtHashMap.emp, h1, h2, h3, ?_⟩
      rw [Std.ExtHashMap.sep_emp]; exact hm
    · refine Or.inr ⟨?_, J, h1, h2, h3, ?_⟩
      · unfold ret32; intro he; rw [he] at h0; exact absurd h0 (by decide)
      · rw [initSafe_perm4] at hm
        exact initSafe_sep_imp (fun _ h => h) (initSafe_sep_imp (fun _ h => h)
          (initSafe_sep_imp (initSafe_sep_imp (initSafe_sep_imp
            (fun _ hc => ⟨by decide, _, Int.toBytes_length _ _, hc⟩) (fun _ h => h))
            (fun _ h => h)) (fun _ h => h))) _ hm

end Kraken.Examples.Sbr.SessionBin
