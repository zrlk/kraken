import WeakCore.TermViewInvF
import WeakCore.TermViewInvE1
import WeakCore.TermViewInvE2
import WeakCore.TermViewInvE3

/-!
# TermViewInvG: `evalOp_V`, assembled from the per-constructor `eo_*` lemmas
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem eo_isTy {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a : At} {τ : Ty}
    (h : (s', t, ws) ∈ evalOp g env σs s (.isTy a τ)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨t0, ws0⟩, hp, pw, hpw, h⟩ := h
  have hw : WV s.mem.size pw := evalAt_V he hp pw (List.mem_of_getLast? hpw)
  repeat' split at h
  all_goals (simp only [pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h)
  all_goals first | exact concl_same hs (WsV_single hw) | exact concl_same hs (WsV_single (WV_cst _ _))

theorem evalOp_V : OpV := by
  intro g env σs s s' t ws op h hs he
  cases op
  case spawn => simp [evalOp] at h
  case ext => simp [evalOp] at h
  case atom => exact eo_atom h hs he
  case pair => exact eo_pair h hs he
  case add => exact eo_add h hs he
  case sub => exact eo_sub h hs he
  case null => exact eo_null h hs he
  case isTy => exact eo_isTy h hs he
  case fold => exact eo_fold h hs he
  case fld => exact eo_fld h hs he
  case mkWord => exact eo_mkWord h hs he
  case mkWord2 => exact eo_mkWord2 h hs he
  case mkEPair => exact eo_mkEPair h hs he
  case mkTicket => exact eo_mkTicket h hs he
  case claim => exact eo_claim h hs he
  case pack => exact eo_pack h hs he
  case packT => exact eo_packT h hs he
  case validate => exact eo_validate h hs he
  case call => exact eo_call h hs he
  case borrow => exact eo_borrow h hs he
  case freeze => exact eo_freeze h hs he
  case endBorrow => exact eo_endBorrow h hs he
  case fnptr => exact eo_fnptr h hs he
  case callc => exact eo_callc h hs he
  case rem => exact eo_rem h hs he
  case nameI => exact eo_nameI h hs he
  case cvt => exact eo_cvt h hs he
  case toInt => exact eo_toInt h hs he
  case asLanes => exact eo_asLanes h hs he
  case fop => exact eo_fop h hs he
  case fcmp => exact eo_fcmp h hs he
  case fop1 => exact eo_fop1 h hs he
  case lane => exact eo_lane h hs he
  case setLane => exact eo_setLane h hs he
  case bits => exact eo_bits h hs he
  case bit1 => exact eo_bit1 h hs he
  case vmatch => exact eo_vmatch h hs he
  case band => exact eo_band h hs he
  case zero => exact eo_zero h hs he
  case idx => exact eo_idx h hs he
  case inl => exact eo_inl h hs he
  case inr => exact eo_inr h hs he
  case new => exact eo_new h hs he
  case publish => exact eo_publish h hs he
  case intoRgn => exact eo_intoRgn h hs he
  case fence => exact eo_fence h hs he
  case load => exact eo_load h hs he
  case store => exact eo_store h hs he
  case ldp => exact eo_ldp h hs he
  case stp => exact eo_stp h hs he
  case fetch => exact eo_fetch h hs he
  case newBuf => exact eo_newBuf h hs he
  case bufInit => exact eo_bufInit h hs he
  case xchg => exact eo_xchg h hs he
  case ldl => exact eo_ldl h hs he
  case ldlw => exact eo_ldlw h hs he
  case stl => exact eo_stl h hs he
  case stlw => exact eo_stlw h hs he
  case xchgAt => exact eo_xchgAt h hs he
  case loadAt => exact eo_loadAt h hs he
  case xchgAtF => exact eo_xchgAtF h hs he
  case loadAtF => exact eo_loadAtF h hs he

end TermViewInv

#print axioms TermViewInv.evalOp_V
