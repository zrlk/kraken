import WeakCore.TermSpawnPh
import WeakCore.TermSpawnDefs
import WeakCore.Complete
/-! # TermSpawnF0 — typing the phantom frame and re-typing the setup frame -/
namespace TermSpawnSim
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section facts
variable {c c' : Cx} (hf : c.facts = c'.facts)
include hf

theorem IEq_facts {d : Nat} {i j : Idx} (h : IEq c d i j) : IEq c' d i j := by
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨h1, fun ρ hs => h2 ρ (hf ▸ hs)⟩

theorem MEq_facts {d : Nat} {μ ν : Mode} (h : MEq c d μ ν) : MEq c' d μ ν := by
  cases h with
  | own => exact .own
  | pub => exact .pub
  | rgn h => exact .rgn (IEq_facts hf h)

theorem LeI_facts {i j : Idx} (h : LeI c i j) : LeI c' i j := fun ρ hs => h ρ (hf ▸ hs)

theorem TyEqS_facts {d : Nat} {a b : Ty} (h : TyEqS c d a b) : TyEqS c' d a b := by
  induction h with
  | refl => exact .refl
  | intS h => exact .intS (IEq_facts hf h)
  | prod _ _ h1 h2 => exact .prod h1 h2
  | sum _ _ h1 h2 => exact .sum h1 h2
  | code _ _ h1 h2 => exact .code h1 h2
  | array h _ h2 => exact .array (IEq_facts hf h) h2
  | ptr h _ h2 => exact .ptr (MEq_facts hf h) h2
  | ptrOpt h _ h2 => exact .ptrOpt (MEq_facts hf h) h2
  | loc h _ h2 => exact .loc (MEq_facts hf h) h2
  | word h => exact .word (IEq_facts hf h)
  | word2 h => exact .word2 (IEq_facts hf h)
  | tok2 h1 h2 h3 => exact .tok2 (IEq_facts hf h1) (IEq_facts hf h2) (IEq_facts hf h3)
  | epair h => exact .epair (IEq_facts hf h)
  | tokE h1 h2 => exact .tokE (IEq_facts hf h1) (IEq_facts hf h2)
  | tokNone h => exact .tokNone (IEq_facts hf h)
  | tokSome h1 h2 => exact .tokSome (IEq_facts hf h1) (IEq_facts hf h2)
  | share h => exact .share (IEq_facts hf h)
  | cap h => exact .cap (IEq_facts hf h)
  | mu _ h => exact .mu h
  | tex _ h => exact .tex h
  | iall _ h => exact .iall h
  | iex _ h => exact .iex h
  | refine _ h => exact .refine h
  | refineIni h _ h2 => exact .refineIni (IEq_facts hf h) h2

theorem SubS_facts {a b : Ty} (h : SubS c a b) : SubS c' a b := by
  induction h with
  | eq h => exact .eq (TyEqS_facts hf h)
  | intS => exact .intS
  | refine _ h => exact .refine h
  | iniWeak h1 h2 => exact .iniWeak (TyEqS_facts hf h1) (LeI_facts hf h2)
  | nonNull h1 h2 => exact .nonNull (MEq_facts hf h1) (TyEqS_facts hf h2)
  | prod _ _ h1 h2 => exact .prod h1 h2
  | sum _ _ h1 h2 => exact .sum h1 h2
  | cap h1 h2 => exact .cap h1 (IEq_facts hf h2)
end facts

theorem noIallV_TyEqS {c : Cx} {d : Nat} {a b : Ty} (h : TyEqS c d a b) : noIallV a = noIallV b := by
  induction h <;> simp_all [noIallV]

theorem noIallV_of_SubS {c : Cx} {a b : Ty} (h : SubS c a b) (hb : noIallV b = true) : noIallV a = true := by
  induction h with
  | eq h => rw [noIallV_TyEqS h]; exact hb
  | intS => rfl
  | refine _ ih => exact ih hb
  | iniWeak h1 _ => simp only [noIallV] at hb ⊢; rw [noIallV_TyEqS h1]; exact hb
  | nonNull => rfl
  | prod _ _ ih1 ih2 => simp only [noIallV, Bool.and_eq_true] at hb ⊢; exact ⟨ih1 hb.1, ih2 hb.2⟩
  | sum _ _ ih1 ih2 => simp only [noIallV, Bool.and_eq_true] at hb ⊢; exact ⟨ih1 hb.1, ih2 hb.2⟩
  | cap => rfl

theorem instantiate_nil {cx : Cx} {d : Decl} {ts : List Ty} {at_ rt : Ty}
    (h : instantiate cx d [] ts = .ok (at_, rt)) : rt = substTs ts.reverse 0 0 (instT [] 0 d.retTy) := by
  unfold instantiate at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i us hus
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hus
  subst hus
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem instantiate_ret {cx : Cx} {R : Ty} {d : Decl} {is : List String} {ts : List Ty} :
    instantiate { cx with ret := R } d is ts = instantiate cx d is ts := rfl

theorem use_ret {cx c₁ : Cx} {a : At} {t : Ty} (R : Ty) (h : cx.use a = .ok (t, c₁)) :
    ({ cx with ret := R } : Cx).use a = .ok (t, { c₁ with ret := R }) := by
  have hp : ({ cx with ret := R } : Cx).peek a = cx.peek a := rfl
  have hke : ({ cx with ret := R } : Cx).ke = cx.ke := rfl
  unfold Cx.use at h ⊢
  rw [hp]
  cases hk : cx.peek a with
  | error e => rw [hk] at h; cases h
  | ok t' =>
    rw [hk] at h
    simp only [bind, Except.bind] at h ⊢
    cases a with
    | var y =>
      simp only at h ⊢
      cases haf : affine cx.ke t' with
      | true =>
        simp only [haf, ite_true, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | false =>
        simp only [haf, Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | _ =>
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

section retypeW
open TermScope Complete

/-- `tyEq` reads its context only through `norm` (the facts). -/
theorem tyEq_norm {cx cx' : Cx} (h : ∀ i, cx.norm i = cx'.norm i) :
    ∀ (a b : Ty) (d : Nat), tyEq cx d a b = tyEq cx' d a b := by
  have he : ∀ i j, cx.eqI i j = cx'.eqI i j := fun i j => by simp only [Cx.eqI, h]
  have hm : ∀ d μ ν, meqD cx d μ ν = meqD cx' d μ ν := by
    intro d μ ν; cases μ <;> cases ν <;> simp [meqD, ieqD, he]
  have hi : ∀ d ψ ψ', iniEq cx d ψ ψ' = iniEq cx' d ψ ψ' := by
    intro d ψ ψ'; cases ψ <;> cases ψ' <;> simp [iniEq, ieqD, he]
  intro a
  induction a <;> intro b d <;> cases b <;> simp_all [tyEq, ieqD]

/-- `sub` reads its context only through `norm`. -/
theorem sub_norm {cx cx' : Cx} (h : ∀ i, cx.norm i = cx'.norm i) :
    ∀ (a b : Ty), sub cx a b = sub cx' a b := by
  have ht := tyEq_norm h
  have he : ∀ i j, cx.eqI i j = cx'.eqI i j := fun i j => by simp only [Cx.eqI, h]
  have hl : ∀ i j, cx.leI i j = cx'.leI i j := fun i j => by simp only [Cx.leI, h]
  have hm : ∀ d μ ν, meqD cx d μ ν = meqD cx' d μ ν := by
    intro d μ ν; cases μ <;> cases ν <;> simp [meqD, ieqD, he]
  intro a
  induction a <;> intro b <;> cases b <;> (try simp_all [sub, ieqD])
  all_goals (rename_i _ ψ1 _ _ ψ2; cases ψ1 <;> cases ψ2 <;> simp_all [sub])

/-- (spawn-site checker rule) **`checkW` of the setup's tail call at its callee's declared return type.** -/
theorem checkW_tail_retype {p : Prog} {cx : Cx} {f : String} {a : At} {ts : List Ty} {d : Decl}
    (h : checkW p cx (.tail f [] a ts) = .ok ()) (hd : p.find f = .ok d) :
    checkW p { cx with ret := substTs ts.reverse 0 0 (instT [] 0 d.retTy) } (.tail f [] a ts) = .ok () := by
  unfold checkW at h ⊢
  have hrw : ∀ r, instantiate { cx with ret := r } d [] ts = instantiate cx d [] ts := fun r => instantiate_ret
  cases hi : instantiate cx d [] ts with
  | error e =>
    simp only [hd, hi, bind, Except.bind] at h; split at h <;> simp at h
  | ok r =>
    obtain ⟨at_, rt⟩ := r
    have hrt := instantiate_nil hi
    cases hu : cx.use a with
    | error e =>
      simp only [hd, hi, hu, bind, Except.bind] at h; split at h <;> simp at h
    | ok q =>
      obtain ⟨t, c₁⟩ := q
      have hs : sub { c₁ with ret := substTs ts.reverse 0 0 (instT [] 0 d.retTy) } rt
          (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true := by
        rw [← hrt]; exact subA_iff.1 (.eq .refl)
      have hsub : ∀ u v, sub { c₁ with ret := substTs ts.reverse 0 0 (instT [] 0 d.retTy) } u v = sub c₁ u v :=
        sub_norm (fun _ => rfl)
      simp only [hd, hi, hu, hrw, use_ret _ hu, bind, Except.bind, hsub] at h ⊢
      have hnl : noLeak { c₁ with ret := substTs ts.reverse 0 0 (instT [] 0 d.retTy) } t = noLeak c₁ t := rfl
      have hnd : noDrop { c₁ with ret := substTs ts.reverse 0 0 (instT [] 0 d.retTy) } = noDrop c₁ := rfl
      rw [hnl, hnd]
      rw [hsub] at hs
      revert h
      by_cases hB : sub c₁ t at_ = true <;>
        cases noLeak c₁ t <;> cases noDrop c₁ <;> simp [hB, hs, throw, throwThe, MonadExceptOf.throw] <;>
        (by_cases hA : ∃ x, x ∈ ts ∧ argOK x = false
         · simp only [hA, ↓reduceIte]; exact id
         · simp only [hA, ↓reduceIte]; intro h; first | rfl | exact h | cases h)

end retypeW

/-- Re-typing a tail call at its callee's declared return type. -/
theorem typed_tail_retype {p : Prog} {cx : Cx} {f : String} {a : At} {ts : List Ty} {d : Decl}
    (hT : Typed p cx (.tail f [] a ts)) (hd : p.find f = .ok d) :
    Typed p { cx with ret := substTs ts.reverse 0 0 (instT [] 0 d.retTy) } (.tail f [] a ts) := by
  cases hT with
  | @tail _ c₁ _ _ _ _ d' at_ rt t hfind hinst hu hnl hsub _ =>
    rw [hd] at hfind; cases hfind
    have hrt := instantiate_nil hinst
    refine .tail hd (by rw [instantiate_ret]; exact hinst) (use_ret _ hu) hnl (SubS_facts (c := c₁) (c' := { c₁ with ret := substTs ts.reverse 0 0 (instT [] 0 d.retTy) }) rfl hsub) ?_
    rw [hrt]; exact .eq .refl

/-! ## Closed types and shifts -/

theorem wf_shiftT (t : Ty) : ∀ (c nt ni : Nat), t.wf nt ni = true → (t.shiftT c).wf (nt + 1) ni = true := by
  induction t with
  | tvar k =>
    intro c nt ni h; simp only [Ty.wf, decide_eq_true_eq] at h
    simp only [Ty.shiftT]; split <;> simp [Ty.wf] <;> omega
  | mu t ih =>
    intro c nt ni h
    simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    exact ⟨by rw [unguarded_shiftT_lt t (c + 1) 0 (by omega)]; exact h.1, ih (c + 1) (nt + 1) ni h.2⟩
  | tex κ t ih =>
    intro c nt ni h
    simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    exact ⟨by rw [unguarded_shiftT_lt t (c + 1) 0 (by omega)]; exact h.1, ih (c + 1) (nt + 1) ni h.2⟩
  | prod a b iha ihb =>
    intro c nt ni h; simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨iha _ _ _ h.1, ihb _ _ _ h.2⟩
  | sum a b iha ihb =>
    intro c nt ni h; simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨iha _ _ _ h.1, ihb _ _ _ h.2⟩
  | code a b iha ihb =>
    intro c nt ni h; simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨iha _ _ _ h.1, ihb _ _ _ h.2⟩
  | array i t ih =>
    intro c nt ni h; simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih _ _ _ h.2⟩
  | ptr μ t ih =>
    intro c nt ni h; simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih _ _ _ h.2⟩
  | ptrOpt μ t ih =>
    intro c nt ni h; simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih _ _ _ h.2⟩
  | loc μ t ih =>
    intro c nt ni h; simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih _ _ _ h.2⟩
  | iall t ih => intro c nt ni h; simp only [Ty.wf, Ty.shiftT] at h ⊢; exact ih _ _ _ h
  | iex t ih => intro c nt ni h; simp only [Ty.wf, Ty.shiftT] at h ⊢; exact ih _ _ _ h
  | refine t ψ ih =>
    intro c nt ni h; simp only [Ty.wf, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih _ _ _ h.2⟩
  | _ => intro c nt ni h; simp_all [Ty.wf, Ty.shiftT]

theorem substTs_tb (t : Ty) : ∀ (σs : List Ty) (c d : Nat), tb c t = true → substTs σs c d t = t := by
  induction t with
  | tvar k => intro σs c d h; simp only [tb, decide_eq_true_eq] at h; simp [substTs, h]
  | mu t ih => intro σs c d h; simp only [tb] at h; simp only [substTs]; rw [ih σs (c + 1) d h]
  | tex κ t ih => intro σs c d h; simp only [tb] at h; simp only [substTs]; rw [ih σs (c + 1) d h]
  | prod a b iha ihb =>
    intro σs c d h; simp only [tb, Bool.and_eq_true] at h; simp only [substTs]; rw [iha σs c d h.1, ihb σs c d h.2]
  | sum a b iha ihb =>
    intro σs c d h; simp only [tb, Bool.and_eq_true] at h; simp only [substTs]; rw [iha σs c d h.1, ihb σs c d h.2]
  | code a b iha ihb =>
    intro σs c d h; simp only [tb, Bool.and_eq_true] at h; simp only [substTs]; rw [iha σs c d h.1, ihb σs c d h.2]
  | array i t ih => intro σs c d h; simp only [tb] at h; simp only [substTs]; rw [ih σs c d h]
  | ptr μ t ih => intro σs c d h; simp only [tb] at h; simp only [substTs]; rw [ih σs c d h]
  | ptrOpt μ t ih => intro σs c d h; simp only [tb] at h; simp only [substTs]; rw [ih σs c d h]
  | loc μ t ih => intro σs c d h; simp only [tb] at h; simp only [substTs]; rw [ih σs c d h]
  | iall t ih => intro σs c d h; simp only [tb] at h; simp only [substTs]; rw [ih σs c (d + 1) h]
  | iex t ih => intro σs c d h; simp only [tb] at h; simp only [substTs]; rw [ih σs c (d + 1) h]
  | refine t ψ ih => intro σs c d h; simp only [tb] at h; simp only [substTs]; rw [ih σs c d h]
  | _ => intros; rfl

theorem close_tb {t : Ty} (h : tb 0 t = true) (σs : List Ty) : close σs t = t := substTs_tb t σs 0 0 h

/-! ## Using and binding variables -/

theorem use_var_true {cx : Cx} {x x' : String} {t : Ty} (h : cx.vars.find? (·.1 == x) = some (x', t, true)) :
    ∃ c₁, cx.use (.var x) = .ok (t, c₁) ∧ c₁.unsealed = cx.unsealed ∧ c₁.torn = cx.torn ∧ c₁.opq = cx.opq ∧
      c₁.ret = cx.ret ∧ c₁.ke = cx.ke ∧ c₁.vars.map (·.1) = cx.vars.map (·.1) := by
  have hp : cx.peek (.var x) = .ok t := by
    simp only [Cx.peek, Cx.find, h, bind, Except.bind, pure, Except.pure, Bool.not_true,
      Bool.false_eq_true, ite_false]
  unfold Cx.use
  rw [hp]
  simp only [bind, Except.bind]
  split
  · refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp only [List.map_map]; congr 1; funext e; obtain ⟨y, u, b⟩ := e
    simp only [Function.comp]; split <;> rfl
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bind_ok {cx : Cx} {x : String} {t : Ty} (hx : (cx.vars.map (·.1)).any (· == x) = false)
    (ht : cx.torn = []) (ho : cx.opq = []) (ha : t.arrFree = true) :
    cx.bind x t = .ok { cx with vars := (x, t, true) :: cx.vars } := by
  have hx' : cx.vars.any (·.1 == x) = false := by rw [List.any_map] at hx; exact hx
  unfold Cx.bind Cx.opaqueOK
  simp [hx', ht, ho, ha]

/-! ## Typing the phantom frame -/

theorem admitsIn_top_unit (cx : Cx) : admitsIn cx Kind.top .unit = true := by
  unfold admitsIn; simp [Ty.wf, Ty.arrFree, Kind.top, Ty.sharedOKIn, Ty.secondClass] <;> decide

theorem noLeak_nil {cx : Cx} (h : cx.unsealed = []) (t : Ty) : NoLeak cx t := by
  intro r _; rw [h]; simp

/-- The context `f0`'s body runs in. -/
def cx0 (R0 : Ty) : Cx := { vars := [("r", R0, true)], ret := .tex Kind.top (R0.shiftT 0) }

theorem typed_f0 {p : Prog} {R0 : Ty} (hR0 : R0.wf 0 0 = true) (ha : R0.arrFree = true) :
    Typed p (cx0 R0) (TermSpawn.f0 R0).body := by
  obtain ⟨c₁, hu, hun, hto, hop, hre, hke, hnm⟩ :=
    use_var_true (cx := cx0 R0) (x := "r") (x' := "r") (t := R0) (by simp [cx0])
  have hb := bind_ok (cx := c₁) (x := "q") (t := .tex Kind.top (R0.shiftT 0))
    (by rw [hnm]; simp [cx0]) (by rw [hto]; rfl) (by rw [hop]; rfl)
    (by simp only [Ty.arrFree]; rw [arrFree_shiftT]; exact ha)
  refine .let_ (OpT.packT (guardT_shiftT_at R0 0) ?_ (admitsIn_top_unit _) hu
    (noLeak_nil (by rw [hun]; rfl) _) (by rw [substT_shiftT]; exact .eq .refl) hb) ?_
  · simp only [Ty.wf, cx0, List.length_nil, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨unguarded_shiftT_at R0 0, wf_shiftT R0 0 0 0 hR0⟩
  · obtain ⟨c₂, hu2, hun2, -, -, hre2, -, -⟩ :=
      use_var_true (cx := { c₁ with vars := ("q", .tex Kind.top (R0.shiftT 0), true) :: c₁.vars })
        (x := "q") (x' := "q") (t := .tex Kind.top (R0.shiftT 0)) (by simp)
    refine .ret hu2 (noLeak_nil (by rw [hun2]; exact hun) _) ?_
    rw [hre2]; show SubS _ _ c₁.ret; rw [hre]; exact .eq .refl

theorem tvOK_cx0 {R0 : Ty} (hR0 : R0.wf 0 0 = true) (hn : noIallV R0 = true) : TvOK (cx0 R0) := by
  have htb : tb 0 R0 = true := tb_of_wf R0 hR0
  have hmg : mg R0 = true := mg_of_wf R0 hR0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he; simp only [cx0, List.mem_singleton] at he; subst he; exact htb
  · intro tn htn; simp [cx0] at htn
  · show tb 0 (.tex Kind.top (R0.shiftT 0)) = true
    simp only [tb]; exact tb_shiftT_up R0 0 0 htb
  · intro e _; simp [cx0, Cx.opaqueOK]
  · intro e he; simp only [cx0, List.mem_singleton] at he; subst he; exact hmg
  · intro tn htn; simp [cx0] at htn
  · show mg (.tex Kind.top (R0.shiftT 0)) = true
    simp only [mg]; rw [mg_shiftT]; exact hmg
  · show noIallV (.tex Kind.top (R0.shiftT 0)) = true
    simp only [noIallV]; rw [noIallV_shiftT]; exact hn

section f0W
open TermScope Complete TermA4

/-- (spawn-site checker rule) A key-free type carries no taken token and no token at all. -/
theorem takenOf_of_rcar : ∀ (t : Ty) (env : List Bool) (d : Nat), rcarE env t = false →
    takenOf d t = [] ∧ taken2Of d t = [] ∧ toksOf t = [] := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro env d h; simp only [rcarE, Bool.or_eq_false_iff] at h
    obtain ⟨a1, a2, a3⟩ := iha env d h.1; obtain ⟨b1, b2, b3⟩ := ihb env d h.2
    simp [takenOf, taken2Of, toksOf, a1, a2, a3, b1, b2, b3]
  | sum a b iha ihb =>
    intro env d h; simp only [rcarE, Bool.or_eq_false_iff] at h
    obtain ⟨a1, a2, a3⟩ := iha env d h.1; obtain ⟨b1, b2, b3⟩ := ihb env d h.2
    simp [takenOf, taken2Of, toksOf, a1, a2, a3, b1, b2, b3]
  | refine t ψ ih => intro env d h; simp only [rcarE] at h; obtain ⟨a1, a2, a3⟩ := ih env d h; simp [takenOf, taken2Of, toksOf, a1, a2, a3]
  | mu t ih => intro env d h; simp only [rcarE] at h; obtain ⟨a1, a2, a3⟩ := ih _ d h; simp [takenOf, taken2Of, toksOf, a1, a2]
  | tex κ t ih => intro env d h; simp only [rcarE] at h; obtain ⟨a1, a2, a3⟩ := ih _ d h; simp [takenOf, taken2Of, toksOf, a1, a2]
  | iall t ih => intro env d h; simp only [rcarE] at h; obtain ⟨a1, a2, a3⟩ := ih env (d + 1) h; simp [takenOf, taken2Of, toksOf, a1, a2]
  | iex t ih => intro env d h; simp only [rcarE] at h; obtain ⟨a1, a2, a3⟩ := ih env (d + 1) h; simp [takenOf, taken2Of, toksOf, a1, a2]
  | _ => intro env d h; simp_all [takenOf, taken2Of, toksOf, rcarE]

/-- (spawn-site checker rule) **The phantom frame's body passes `checkW`** at an `argOK` return type. -/
theorem checkW_f0 {p : Prog} {R0 : Ty} (hR0 : R0.wf 0 0 = true) (ha : R0.arrFree = true) (hw : argOK R0 = true) :
    checkW p (cx0 R0) (TermSpawn.f0 R0).body = .ok () := by
  have hwf0 : (Ty.tex Kind.top (R0.shiftT 0)).wf 0 0 = true := by
    simp only [Ty.wf, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨unguarded_shiftT_at R0 0, wf_shiftT R0 0 0 0 hR0⟩
  have hadm : ∀ c : Cx, admitsIn c Kind.top .unit = true := admitsIn_top_unit
  show checkW p (cx0 R0) (.let_ "q" (.packT (.var "r") .unit (.tex Kind.top (R0.shiftT 0))) (.ret (.var "q"))) = .ok ()
  have htb : tb 0 R0 = true := tb_of_wf R0 hR0
  have hg : Ty.guardT 0 (R0.shiftT 0) = true := guardT_shiftT_at R0 0
  have hwf := hwf0
  have hs : R0.shiftT 0 = R0 := tb_shiftT R0 htb (Nat.le_refl 0)
  rw [hs] at hg hwf ⊢
  simp only [argOK, Bool.and_eq_true, Bool.not_eq_true'] at hw
  have hrc : rcarE [] R0 = false := hw.2
  have hk := takenOf_of_rcar R0 [] 0 hrc
  have hwt : wrapOK (.tex Kind.top R0) = true := by
    show (!rcarE [false] R0 && wrapOKE [false] R0) = true
    rw [rcarE_closed htb, wrapOKE_closed htb, hw.1, hw.2]; rfl
  have hsub : ∀ c : Cx, sub c (.tex Kind.top R0) (.tex Kind.top R0) = true :=
    fun c => subA_iff.1 (.eq .refl)
  have hsub2 : ∀ c : Cx, sub c R0 R0 = true := fun c => subA_iff.1 (.eq .refl)
  have hsu : Ty.substT 0 .unit R0 = R0 := by
    have := substT_shiftT R0 0 .unit; rw [hs] at this; exact this
  have hu1 : wrapOK Ty.unit = true := rfl
  have hu2 : rcar Ty.unit = false := rfl
  cases haf : affine [] R0 <;> cases haf2 : affine [] (Ty.tex Kind.top R0) <;>
  simp [checkW, opArgOK, checkOp, cx0, hg, hwf, hwt, Cx.use, Cx.peek, Cx.find, haf, noLeak, Cx.bind,
    noDrop, hk, bind, Except.bind, pure, Except.pure, argOK, hsub2, hsu, hadm, hu1, hu2, Cx.opaqueOK, Ty.arrFree, ha, hs] <;>
  (try rw [haf2]) <;> simp [toksOf, takenOf, taken2Of, hk, hsub]

/-- (spawn-site checker rule) **The phantom frame is the checker's** (`CkW`). -/
theorem ckW_f0 {p : Prog} {R0 : Ty} {w : Nat → Ty} (hR0 : R0.wf 0 0 = true) (ha : R0.arrFree = true)
    (hw : argOK R0 = true) : CkW p w (cx0 R0) (TermSpawn.f0 R0).body := by
  refine ⟨checkW_f0 hR0 ha hw, fun v hv => ?_, fun k hk => absurd hk (by simp [cx0])⟩
  simp only [cx0, List.mem_singleton] at hv
  subst hv
  simp only [argOK, Bool.and_eq_true] at hw
  exact hw.1

end f0W

/-- A frame with no variables, no type parameters and a trivial continuation. -/
theorem finvR_empty {ρ : Nat → Nat} {η : TEnv} {p : Prog} {T : Ty} {Rf : Res} (hW : WitAF η) :
    FInvR ρ η [] (ResumeR p [] .zero) ({ ret := T } : Cx) [] Rf := by
  refine ⟨⟨Sat_nil ρ, fun x e h => by simp at h, fun _ _ _ _ _ => trivial,
    ⟨fun k _ h => absurd h (Nat.not_lt_zero _), fun k σ h => by simp at h,
      fun k _ h => absurd h (Nat.not_lt_zero _)⟩,
    Nat.le_refl 0, ⟨fun k h => by simp [KEnv.ask] at h, fun k h => by simp [KEnv.ask] at h,
      fun σ h => by simp at h⟩,
    hW, fun k h => by simp [KEnv.ask] at h, fun k h => by simp [KEnv.ask] at h,
    fun k h => by simp [KEnv.ask] at h, fun k h => by simp [KEnv.ask] at h⟩,
    fun _ _ _ _ _ _ => rfl, ⟨List.nodup_nil, List.nodup_nil, by simp, fun _ => .zero, by simp,
      by simp [Res.zero_le]⟩⟩

/-- **The phantom frame resumes**: returning a value at `R0` into `[f0 R0]` holding `Rs`. -/
theorem retOKR_f0 {p : Prog} {R0 : Ty} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {Rs : Res}
    (hR0 : R0.wf 0 0 = true) (ha : R0.arrFree = true) (hn : noIallV R0 = true)
    (hw : TermScope.argOK R0 = true)
    (hE : EnvOK p η) (hW : WitAF η) :
    RetOKR ρ η σs R0 (ResumeR p [TermSpawn.f0 R0] Rs) := by
  intro η' hx ws R hv hl
  have htb : tb 0 R0 = true := tb_of_wf R0 hR0
  have e1 : close σs R0 = R0 := close_tb htb σs
  have e2 : close [] R0 = R0 := close_tb htb []
  rw [e1] at hv
  have hl' : Lay [] R0 R0 ws := by unfold Lay at hl ⊢; rw [e2]; rw [e1] at hl; exact hl
  have hr2 : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hW' : WitAF η' := by intro k; rw [hx.2.1]; exact hW k
  refine ⟨Rs, .zero, (Res.add_zero _).symm, ρ, η', cx0 R0, rfl, rfl,
    ⟨hx.2.2.1.trans hE.1, hx.1, hr2⟩, ⟨typed_f0 hR0 ha, ckW_f0 hR0 ha hw⟩, tvOK_cx0 hR0 hn, ?_, fun _ _ h => by cases h⟩
  have hb := bind_ok (cx := ({ ret := .tex Kind.top (R0.shiftT 0) } : Cx)) (x := "r") (t := R0)
    rfl rfl rfl ha
  exact bindR hb (finvR_empty (p := p) (Rf := Rs) hW') (RLink_of hx.1 hr2) hv hl'

/-- **Re-typing the setup thread with the phantom frame below it.** -/
theorem thInvRE_app {p : Prog} {E : TEnv} {th0 : TTh} {Tot : Res} {f : String} {ts : List Ty} {d : Decl}
    (h : ThInvRE p E th0 Tot) (hstk : th0.stack = []) (hset : th0.term = .tail f [] (.var "a") ts)
    (hd : p.find f = .ok d) (hR0 : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true)
    (ha : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true)
    (hw : TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true) :
    ThInvRE p E (app (TermSpawn.f0 (substTs ts.reverse 0 0 (instT [] 0 d.retTy))) th0) Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hEO, hTy, hTv, hF, hsum, -⟩ := h
  rw [hset] at hTy
  have hTy' := typed_tail_retype hTy.1 hd
  have hn : noIallV (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true := by
    cases hTy.1 with
    | @tail _ c₁ _ _ _ _ d' at_ rt t hfind hinst hu _ _ hsubr =>
      rw [hd] at hfind; cases hfind
      have hrt := instantiate_nil hinst
      have hret : c₁.ret = cx.ret := (use_inv (ρ := ρ) (η := η) (σs := th0.σs) (env := th0.env) hu).2.2.1
      rw [← hrt]
      exact noIallV_of_SubS hsubr (by rw [hret]; exact hTv.2.2.2.2.2.2.2)
  refine ⟨ρ, η, { cx with ret := substTs ts.reverse 0 0 (instT [] 0 d.retTy) }, Rf, Rs, hCE, hEO,
    ?_, ?_, ?_, hsum, ?_⟩
  · show TypedK p η _ th0.term; rw [hset]; exact ⟨hTy', checkW_tail_retype hTy.2.1 hd, hTy.2.2.1, hTy.2.2.2⟩
  · exact ⟨hTv.1, hTv.2.1, tb_mono _ (tb_of_wf _ hR0) (Nat.zero_le _), hTv.2.2.2.1, hTv.2.2.2.2.1,
      hTv.2.2.2.2.2.1, mg_of_wf _ hR0, hn⟩
  · show FInvR ρ η th0.σs (ResumeR p (th0.stack ++ [_]) Rs) _ th0.env Rf
    rw [hstk]
    exact ⟨⟨hF.1.1, hF.1.2.1, fun _ _ _ _ _ => trivial, hF.1.2.2.2⟩,
      retOKR_f0 hR0 ha hn hw hEO hF.1.2.2.2.2.2.2.1, hF.2.2⟩
  · intro fr rest h ws
    simp only [app, hstk, List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    show _ = TermPtrRts.pubWords (close th0.σs _) ws
    rw [close_tb (tb_of_wf _ hR0)]
    rfl

theorem thSys_app {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th0 : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {f : String} {ts : List Ty} {d : Decl}
    (h : ThSys p g mem pairs th0 Eg Tot HP HS cr db) (hstk : th0.stack = [])
    (hset : th0.term = .tail f [] (.var "a") ts)
    (hd : p.find f = .ok d) (hR0 : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true)
    (ha : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true)
    (hw : TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true) :
    ThSys p g mem pairs (app (TermSpawn.f0 (substTs ts.reverse 0 0 (instT [] 0 d.retTy))) th0)
      Eg Tot HP HS cr db := by
  obtain ⟨S, hR, -, hm, hP, hS, hC⟩ := h
  have hR' := thInvRE_app hR hstk hset hd hR0 ha hw
  exact ⟨S, hR', hR'.thInvE, hm, hP, hS, hC⟩

/-- `InitOK` at the phantom start. -/
theorem initOK_phant {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {cpre : Cfg} {th0 : TTh} {f : String} {ts : List Ty} {d : Decl}
    (h0 : InitOK p k arch Init MintOK cpre) (hpre : cpre.ths[0]? = some th0) (hstk : th0.stack = [])
    (hset : th0.term = .tail f [] (.var "a") ts)
    (hd : p.find f = .ok d) (hR0 : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true)
    (ha : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true)
    (hw : TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true) :
    InitOK p k arch Init MintOK (TermSpawn.phant (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) cpre) :=
  initOK_phantC h0 rfl fun _ _ _ _ _ _ th h hs => by
    rw [hpre] at h; cases h; exact thSys_app hs hstk hset hd hR0 ha hw

end TermSpawnSim

#print axioms TermSpawnSim.initOK_phant
