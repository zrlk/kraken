import WeakCore.TermSpawnMidBridge
import WeakCore.TermSpawnKid
import WeakCore.TermCkL
/-!
# TermSpawnTy — the spawn typing rule's content at a spawn site, from the thread invariant

At `th.term = let_ x (spawn f a T ts) e`, inverting `OpT.spawn` (the rule) under the thread's
`ThInvRE`/`ThInvE` gives: the kid's entry (`KidEntryOK p T f ts`), the argument as a value of `T`
at the thread-wide view, and the parent's continuation typing (`spawnPar`: `x := num ths.size`).
No program-level obligation is used.
-/
namespace TermSpawnMid
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem wf_of_tb (t : Ty) : ∀ {nt c ni : Nat}, t.wf nt ni = true → tb c t = true → t.wf c ni = true := by
  induction t with
  | tvar k => intro nt c ni h1 h2; simpa [Ty.wf, tb] using h2
  | prod a b iha ihb => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨iha h1.1 h2.1, ihb h1.2 h2.2⟩
  | sum a b iha ihb => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨iha h1.1 h2.1, ihb h1.2 h2.2⟩
  | code a b iha ihb => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨iha h1.1 h2.1, ihb h1.2 h2.2⟩
  | array _ t ih => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨h1.1, ih h1.2 h2⟩
  | ptr _ t ih => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨h1.1, ih h1.2 h2⟩
  | ptrOpt _ t ih => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨h1.1, ih h1.2 h2⟩
  | loc _ t ih => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨h1.1, ih h1.2 h2⟩
  | mu t ih => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨h1.1, ih h1.2 h2⟩
  | tex _ t ih => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨h1.1, ih h1.2 h2⟩
  | iall t ih => intro nt c ni h1 h2; simp only [Ty.wf, tb] at h1 h2 ⊢; exact ih h1 h2
  | iex t ih => intro nt c ni h1 h2; simp only [Ty.wf, tb] at h1 h2 ⊢; exact ih h1 h2
  | refine t _ ih => intro nt c ni h1 h2; simp only [Ty.wf, tb, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨h1.1, ih h1.2 h2⟩
  | _ => intro nt c ni h1 _; simpa [Ty.wf] using h1

/-- Using a copyable value leaves the context unchanged. -/
theorem use_copy {cx c₁ : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c₁)) (ha : affine cx.ke t = false) :
    c₁ = cx := by
  rcases use_cases h with ⟨-, ⟨-, e⟩ | ⟨y, rfl, e⟩⟩
  · exact e
  · unfold Cx.use at h
    simp only [bind_ok_iff] at h
    obtain ⟨t', ht, h⟩ := h
    split at h
    · rename_i haff
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rw [ha] at haff; cases haff
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm

/-- The premises of `OpT.spawn`, packaged. -/
structure SpawnPrem (p : Prog) (cx : Cx) (x f : String) (a : At) (T : Ty) (ts : List Ty) (c' : Cx) : Prop where
  ut : ∃ t, cx.use a = .ok (t, cx) ∧ SubS cx t T
  aff : affine cx.ke T = false
  wf : T.wf cx.ke.length 0 = true
  tb : tb 0 T = true
  drf : TermScope.drf T = true
  tsDrf : ts.all TermScope.drf = true
  wrap : TermScope.wrapOK T = true
  tsArg : ts.all TermScope.argOK = true
  rtc : ∃ rt, tailCheck p { vars := [("a", T, true)], ret := rt } f [] (.var "a") ts = .ok () ∧
    (TermClose.tb 0 rt && TermTv.mg rt && TermTv.noIallV rt) = true
  bind : cx.bind x .tid = .ok c'

theorem spawnPrem_of {p : Prog} {cx c' : Cx} {x f : String} {a : At} {T : Ty} {ts : List Ty}
    (h : OpT p cx x (.spawn f a T ts) c') : SpawnPrem p cx x f a T ts c' := by
  cases h with
  | spawn hu hsub haff hwf hwfs htb htbs hdrf hdrfs hwr harg hd hi hc hrt hb =>
    simp only [Bool.or_eq_false_iff] at haff
    have hcx := use_copy hu (by
      rcases use_cases hu with ⟨-, ⟨-, e⟩ | ⟨y, -, e⟩⟩ <;> subst e <;> exact haff.1)
    subst hcx
    exact ⟨⟨_, hu, hsub⟩, haff.2, hwf, htb, hdrf, hdrfs, hwr, harg, ⟨_, hc, hrt⟩, hb⟩

/-- **The kid's entry** from the rule. -/
theorem kidEntryOK_of {p : Prog} {cx c' : Cx} {x f : String} {a : At} {T : Ty} {ts : List Ty}
    (h : SpawnPrem p cx x f a T ts c') : KidEntryOK p T f ts := by
  obtain ⟨rt, htc, hrt⟩ := h.rtc
  simp only [Bool.and_eq_true] at hrt
  refine ⟨?_, h.tb, h.drf, h.tsDrf, h.tsArg, h.wrap, ⟨rt, ?_, ?_⟩⟩
  · show Ty.affineIn [] T = false
    rw [AffineCl.affineIn_closed h.tb [] cx.ke]; exact h.aff
  · simpa [check] using htc
  · refine ⟨fun e he => ?_, fun tn htn => (by simp at htn), hrt.1.1, fun e he => ?_, fun e he => ?_,
      fun tn htn => (by simp at htn), hrt.1.2, hrt.2⟩
    · simp only [List.mem_singleton] at he; subst he; exact h.tb
    · simp [Cx.opaqueOK]
    · simp only [List.mem_singleton] at he; subst he; exact mg_of_wf T h.wf


/-- **The argument** is a value of the bound type `T` at the thread-wide view. -/
theorem arg_of_site {p : Prog} {E : TEnv} {th : TTh} {x f : String} {a : At} {T : Ty} {ts : List Ty} {e : Expr}
    {rt : Ty} {ws : List Word}
    (h : ThInvE p E th) (hterm : th.term = .let_ x (.spawn f a T ts) e) (hev : evalAt th.env a = some (rt, ws)) :
    VR (fun _ => 0) E T (shp T) ws ∧ Lay [] T T ws := by
  obtain ⟨ρ, η, cx, hCE, hE, hT, -, hi, -⟩ := h
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
    have P := spawnPrem_of hop
    obtain ⟨t0, hu0, hsub0⟩ := P.ut
    obtain ⟨hF1, rt', ws', hev', hv', hl'⟩ := use_FInv hu0 hi
    rw [hev] at hev'
    simp only [Option.some.injEq, Prod.mk.injEq] at hev'
    obtain ⟨rfl, rfl⟩ := hev'
    have hv2 := VR_sub hF1.1 hsub0 _ _ hv'
    obtain ⟨hs2, hl2⟩ := Lay_canon hsub0 hl'
    have e1 : close th.σs T = T := TermSpawnStep.close_tb0 th.σs P.tb
    have e0 : close [] T = T := TermSpawnStep.close_tb0 [] P.tb
    rw [e1] at hs2 hl2
    rw [hs2] at hv2
    refine ⟨?_, ?_⟩
    · have := VR_toCE hE.2.1 (wf_of_tb T P.wf P.tb) hv2
      rw [hCE] at this; exact this
    · unfold Lay at hl2 ⊢
      rw [e1] at hl2; rw [e0]; exact hl2

/-- **The parent's continuation** (`spawnPar`: `x := loc ⟨L, 0⟩`, the kid's box `L`, a published unit cell
at frontier `0` in `E` (E2, `TermBox`)): any `par` of that shape. -/
theorem par_of_site {p : Prog} {E : TEnv} {th par : TTh} {Tot : Res} {x f : String} {a : At} {T : Ty}
    {ts : List Ty} {e : Expr} {L : AllocLabel} (hterm : th.term = .let_ x (.spawn f a T ts) e)
    (hpt : par.term = e) (hpe : par.env = (x, .tid, [cst (.loc ⟨L, 0⟩ 0)]) :: th.env) (hps : par.σs = th.σs)
    (hpk : par.stack = th.stack) (hbx : E.sto L = some ⟨.unit, none⟩ ∧ E.pfr L = some 0)
    (hR : ThInvRE p E th Tot) (hE' : ThInvE p E th) :
    ThInvRE p E par Tot ∧ ThInvE p E par := by
  have hl : Lay th.σs .tid .tid [cst (.loc ⟨L, 0⟩ 0)] :=
    ⟨fun us h => by simp [accs] at h; subst h; rfl, by first | rfl | simp [etok, close, substTs, skel],
      by simp [wc, accs], trivial, by first | rfl | simp [etok, close, substTs, lyt]⟩
  constructor
  · obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hpw⟩ := hR
    have hT2 := hT.2
    rw [hterm] at hT2
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hT2
    have P := spawnPrem_of hop
    have hret : c'.ret = cx.ret := bind_ret P.bind
    have htv' := (bind_TvOK P.bind htv (by simp [tb]) (by simp [mg])).1
    have hs1 : η.sto L = some ⟨.unit, none⟩ := by rw [← CE_sto, hCE]; exact hbx.1
    have hp1 : η.pfr L = some 0 := by rw [← CE_pfr, hCE]; exact hbx.2
    have hvr : VRR ρ η .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] .zero :=
      ⟨⟨L, ⟨.unit, none⟩, rfl, hs1, rfl, 0, hp1, .inr fun _ _ => Nat.zero_le _⟩, rfl⟩
    have hf := bindRZ P.bind hi (RLink_of hE.2.1 hE.2.2) hvr hl
    refine ⟨ρ, η, c', Rf, Rs, hCE, hE, ⟨by rw [hpt]; exact he, by rw [hpt]; exact hck⟩, htv',
      by rw [hps, hpk, hpe]; exact hf, hsum, ?_⟩
    intro fr rest hst ws
    rw [hpk] at hst
    rw [hret, hps]; exact hpw fr rest hst ws
  · obtain ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hpw⟩ := hE'
    rw [hterm] at hT
    cases hT with
    | let_ hop he =>
      rename_i c'
      have P := spawnPrem_of hop
      have hret : c'.ret = cx.ret := bind_ret P.bind
      have htv' := (bind_TvOK P.bind htv (by simp [tb]) (by simp [mg])).1
      have hs1 : η.sto L = some ⟨.unit, none⟩ := by rw [← CE_sto, hCE]; exact hbx.1
      have hp1 : η.pfr L = some 0 := by rw [← CE_pfr, hCE]; exact hbx.2
      have hvr : VR ρ η .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] :=
        ⟨L, ⟨.unit, none⟩, rfl, hs1, rfl, 0, hp1, .inr fun _ _ => Nat.zero_le _⟩
      refine ⟨ρ, η, c', hCE, hE, by rw [hpt]; exact he, htv', by rw [hps, hpe, hpk]; exact bind_FInv P.bind hi hvr hl, ?_⟩
      show RetPw par.σs par.stack c'.ret
      rw [hret, hps, hpk]; exact hpw

end TermSpawnMid

#print axioms TermSpawnMid.kidEntryOK_of
#print axioms TermSpawnMid.arg_of_site
#print axioms TermSpawnMid.par_of_site
#print axioms TermSpawnMid.wf_of_tb
#print axioms TermSpawnMid.use_copy
#print axioms TermSpawnMid.spawnPrem_of
