import WeakCore.StackFrameLevel
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound
open FlatAnchor (RRSound RelsSound_CE RRSound_CE)

/-! **StackInduction**: the F4 stack induction.

`RetOKRBs`/`FInvRBs`/`ResumeRBs` are local mirrors of the ♭ `RetOKRB`/`FInvRB`/`ResumeRB`
with the supply restriction as a generic predicate `Sup` on the returned env.  F4 uses `Sup` only
through `hSup : Sup η′ → ∃ b, FreshSup P b η′` (the earlier premise `hU` was removed).  The ♭ layer
instantiates `Sup` by the supply clause; the mirrors never appear in an exit statement.

Each level: the ♭ return env `η′` lifts to `η″ = L.etaW b η′ ηW` (base `b` above the supply bound, `L.bnd` and the
returned words' labels); W's continuation at `η″` gives the caller frame `ηf`; its ♭ partner is `reB ηf η′`
(merge `mg`, `σ′`), and the next level is `L.next`.  The stack resource `Rs` is unchanged (`RsSup`: no own key on
the plan tail), the frame words are below `P.N` (`StkLt`, chosen with the plan). -/

section mirror
variable (Sup : TEnv → Prop)

/-- Local mirror: `RetOKRB` at supply envs only. -/
def RetOKRBs (lb n i : Nat) (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (ret : Ty) (K : TEnv → Nat → List Word → Res → Prop) :
    Prop :=
  ∀ η', ExtB η η' → Sup η' → ∀ ws R, VRRB ρ η' ret (shp (close σs ret)) ws R → Lay σs ret (close σs ret) ws →
    K (CE η') η'.rid ws R

/-- Local mirror of `FInvRB`. -/
def FInvRBs (lb n i : Nat) (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (K : TEnv → Nat → List Word → Res → Prop)
    (cx : Cx) (env : Env) (Rf : Res) : Prop :=
  FInvB lb n i ρ η σs (fun _ _ => True) cx env ∧ RetOKRBs Sup lb n i ρ η σs cx.ret K ∧ HeldOKB ρ η cx env Rf

/-- Local mirror of `ResumeRB`. -/
def ResumeRBs (lb n i : Nat) (p : Prog) : List Frame → Res → TEnv → Nat → List Word → Res → Prop
  | [], Rs, _, _, _, _ => Rs = .zero
  | f :: rest, Rs, E, rd, ws, R => ∃ Rc Rrest, Rs = Rc + Rrest ∧ ∃ ρ η c, CE η = E ∧ η.rid = rd ∧
      EnvOKB p η ∧ TypedK p η c f.body ∧ TvOK c ∧
      FInvRBs Sup lb n i ρ η f.σs (ResumeRBs lb n i p rest Rrest) c ((f.x, f.ty, ws) :: f.env) (Rc + R) ∧
      (∀ (f' : Frame) (rest' : List Frame), rest = f' :: rest' → ∀ ws,
        TermPtrRts.pubWords f'.ty ws = TermPtrRts.pubWords (close f.σs c.ret) ws) ∧
      DyFr p annNew (progTgts p) η f.σs f.body
end mirror

/-- The stack's frame words lie below the plan start (internal: `P.N` is chosen above them). -/
def StkLt (P : Plan) (stack : List Frame) : Prop :=
  ∀ f ∈ stack, ∀ e ∈ f.env, ∀ w ∈ e.2.2, ∀ a g, w.val = .loc a g → a.label < P.N

/-- The stack resource owns no plan-tail label (the supply bound at the plan's parameters). -/
def RsSup (P : Plan) (Rs : Res) : Prop := ∀ l, P.Tail P.N l → Rs (.own l) = 0

/-- A bound above every label of a word list. -/
def wsB (ws : List Word) : Nat :=
  ws.foldr (fun w n => max n (match w.val with | .loc a _ => a.label + 1 | _ => 0)) 0

theorem wsB_lt : ∀ (ws : List Word) (w : Word), w ∈ ws → ∀ a g, w.val = .loc a g → a.label < wsB ws
  | [], _, hw, _, _, _ => by simp at hw
  | w₀ :: ws, w, hw, a, g, hv => by
    simp only [List.mem_cons] at hw
    simp only [wsB, List.foldr_cons]
    rcases hw with rfl | hw
    · rw [hv]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    · have := wsB_lt ws w hw a g hv
      unfold wsB at this
      exact Nat.lt_of_lt_of_le this (Nat.le_max_left _ _)

theorem lookupE_mem {env : Env} {y : String} {rt : Ty} {ws : List Word} (h : lookupE env y = some (rt, ws)) :
    ∃ e ∈ env, e.2.2 = ws := by
  unfold lookupE at h
  cases e : env.find? (·.1 == y) with
  | none => rw [e] at h; cases h
  | some e' =>
    rw [e] at h
    have h' := Option.some.inj h
    exact ⟨e', List.mem_of_find?_eq_some e, congrArg Prod.snd h'⟩

theorem map_rl_fix {f : WeakMem.AllocLabel → WeakMem.AllocLabel} :
    ∀ (ws : List Word), (∀ w ∈ ws, ∀ a g, w.val = .loc a g → f a.label = a.label) → ws.map (rl f) = ws
  | [], _ => rfl
  | w :: ws, h => by
    simp only [List.map_cons]
    rw [map_rl_fix ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))]
    congr 1
    cases w with
    | mk v vw rt =>
      cases v with
      | loc a k => have := h _ List.mem_cons_self a k rfl; simp [rl, rlv, this]
      | _ => simp [rl, rlv]

namespace Lv
variable {P : Plan} {L : Lv P} {b : Nat}

section
variable (hM : L.c₀ + 3 ≤ P.M) (hbb : L.bnd ≤ b)
include hM hbb

theorem not_tail_lt {a : WeakMem.AllocLabel} {c : Nat} (ha : a < c) : ¬ P.Tail c a :=
  fun ⟨_, hk, e⟩ => Plan.fl_ne_of_lt (P := P) ha hk e.symm

omit hM hbb in
theorem Used_tail {c : Nat} {a : WeakMem.AllocLabel} (h : P.Used c a) : P.Tail P.N a := by
  obtain ⟨k, hk, -, e⟩ := h; exact ⟨k, hk, e⟩

/-- Labels below the plan start are fixed by the merge map. -/
theorem mg_low {a : WeakMem.AllocLabel} (ha : a < P.N) : L.mg b a = a := by
  have hb := hbN hM hbb
  have hu : ¬ P.Used (L.c₀ + 3) a := fun h => not_tail_lt hM hbb ha (Used_tail h)
  obtain ⟨h0, h1, h2⟩ := fr_gen hM hbb hu
  rw [mg_gen hM hbb h0 h1 h2]; exact «τ'_fix» hM hb hu

/-- `σ′` moves only plan-tail labels, so it fixes a resource with no own key on the tail. -/
theorem sw_fix {X : Res} (hX : RsSup P X) : Res.sw (L.σ' b) X = X := by
  have hb := hbN hM hbb
  funext k
  cases k with
  | own l =>
    show X (.own (L.σ' b l)) = X (.own l)
    rcases Classical.em (P.Used (L.c₀ + 3) l) with hu | hu
    · have hu' : P.Used (L.c₀ + 3) (L.σ' b l) := by
        rcases Classical.em (P.Used (L.c₀ + 3) (L.σ' b l)) with h | h
        · exact h
        · have e := «σ'_fix» hM hb h
          have : L.σ' b l = l := by
            have := congrArg (L.τ' b) e; rw [«τ'σ'» hM hb, «τ'σ'» hM hb] at this; rw [this]
          rw [this] at h; exact absurd hu h
      rw [hX _ (Used_tail hu), hX _ (Used_tail hu')]
    · rw [«σ'_fix» hM hb hu]
  | _ => rfl

theorem RsSup.left {X Y : Res} (h : RsSup P (X + Y)) : RsSup P X := fun l hl => by
  have := h l hl; simp only [Res.add_apply] at this; omega

theorem RsSup.right {X Y : Res} (h : RsSup P (X + Y)) : RsSup P Y := fun l hl => by
  have := h l hl; simp only [Res.add_apply] at this; omega

end

/-- **lift_step**: one ♭ return at level `L` lifts to W's `η″`, with the W words merging back to the ♭ ones. -/
theorem lift_step (hM : L.c₀ + 3 ≤ P.M) {ηW ηB η' : TEnv} {b₀ : Nat} (hr : RelW L ηW ηB)
    (he : ExtB ηB η') (hs0 : FreshSup P b₀ η') {ρ : Nat → Nat} {t : Ty} {rt : Shp} {ws : List Word} {R : Res}
    (hv : VRRB ρ η' t rt ws R) :
    ∃ b, ∃ hbb : L.bnd ≤ b, FreshSup P b η' ∧ ∃ wsW, Ext ηW (L.etaW b η' ηW) ∧
      VRR ρ (L.etaW b η' ηW) t rt wsW (Res.sw (L.τ' b) R) ∧ wsW.map (rl (L.mg b)) = ws ∧
      ∀ σs t' rt', Lay σs t' rt' ws → Lay σs t' rt' wsW := by
  let b := max (max b₀ L.bnd) (wsB ws)
  have hbb : L.bnd ≤ b := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hb := hbN hM hbb
  have hs : FreshSup P b η' := hs0.mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have hw : ηW.wit = η'.wit := hr.wit.trans he.2.1.symm
  have hp : ηW.prog = η'.prog := hr.prog.trans he.2.2.1.symm
  have ht : ηW.tid = η'.tid := hr.tid.trans he.2.2.2.1.symm
  obtain ⟨hm, hci⟩ := lift_ok η' ηW hM hb hs hw hp ht
  have hext := ext_ok hM hb hbb hr he hs
  have hB : CohRB η' := he.2.2.2.2.2.2.2.2.2.2.1
  have hW : CohR (L.etaW b η' ηW) := hext.2.2.2.2.2.2.2.2.2.2.1
  have hsc : ∀ l, CpO η' l → L.σ' b l ≠ L.cpy b l := by
    rintro l ⟨c, hc, -⟩ e
    have hnt : ¬ P.Tail b l := fun hl => by rw [hs.sto l hl] at hc; cases hc
    have : l = L.cpy b l := by
      have h2 : L.τ' b (L.σ' b l) = L.τ' b (L.cpy b l) := congrArg _ e
      rw [«τ'σ'» hM hb, «τ'_cpy» hM hb] at h2
      exact h2
    exact hnt (this ▸ tail_cpy hM hb l)
  have hbc : ∀ l k, CpO η' l → L.bvar b l k ≠ L.cpy b l := fun l k _ e => cpy_ne_bvar hM hb l l k e.symm
  have hv' := VRR_liftTop hsc hbc hm hci hB hW (RLink_of_coh he.1 hB) hv
  refine ⟨b, hbb, hs, _, hext, hv', ?_, fun σs t' rt' hl => Lay_rlI hl⟩
  have hx := gc_ExS (cpy := L.cpy b) (σ := L.σ' b) (Cp := CpO η') (bv := L.bvar b) t _
    (Ttop (L.cpy b) (L.σ' b) (CpO η') (L.bvar b) η'.unsee) η' rt ws (Ttop_ExS η')
  refine rlI_back _ ws (fun i w a k h1 h2 => ?_)
  have hlt : a.label < b :=
    Nat.lt_of_lt_of_le (wsB_lt ws w (List.mem_iff_getElem?.2 ⟨i, h1⟩) a k h2) (Nat.le_max_right _ _)
  rcases hx i with e | ⟨e, -⟩ | ⟨k', e⟩ <;> rw [e]
  · exact mg_σ' hM hbb (fun ⟨_, hk, e'⟩ => Plan.fl_ne_of_lt (P := P) hlt hk e'.symm)
  · exact mg_cpy hM hbb _
  · exact mg_bvar hM hbb _ _


end Lv

/-- **F4** (stack induction): W's resourceful return continuation at a level-`L` caller env gives the ♭ one
(local mirror) at its partner, for every stack, at the same stack resource. -/
theorem f4 {p : Prog} {P : Plan} {Sup : TEnv → Prop}
    (hSup : ∀ η, Sup η → ∃ b, FreshSup P b η) :
    ∀ (stack : List Frame) (L : Lv P) (ηW ηB : TEnv) (ρ : Nat → Nat) (σs : List Ty) (ret : Ty) (Rs : Res),
      L.c₀ + 3 * (stack.length + 1) ≤ P.M → RelW L ηW ηB → ηW.prog = p → StkLt P stack → RsSup P Rs →
      RetOKR ρ ηW σs ret (ResumeR p stack Rs) → RetOKRBs Sup glb gnum gi ρ ηB σs ret (ResumeRBs Sup glb gnum gi p stack Rs) := by
  intro stack
  induction stack with
  | nil =>
    intro L ηW ηB ρ σs ret Rs hM hr hp hStk hRs hK η' he hsup ws R hv hl
    have hM3 : L.c₀ + 3 ≤ P.M := by simp only [List.length_nil] at hM; omega
    obtain ⟨b₀, hs0⟩ := hSup η' hsup
    obtain ⟨b, hbb, hs, wsW, hext, hvW, -, hlay⟩ := Lv.lift_step hM3 hr he hs0 hv
    exact hK _ hext wsW _ hvW (hlay _ _ _ hl)
  | cons f rest ih =>
    intro L ηW ηB ρ σs ret Rs hM hr hp hStk hRs hK η' he hsup ws R hv hl
    have hM3 : L.c₀ + 3 ≤ P.M := by simp only [List.length_cons] at hM; omega
    obtain ⟨b₀, hs0⟩ := hSup η' hsup
    obtain ⟨b, hbb, hs, wsW, hext, hvW, hback, hlay⟩ := Lv.lift_step hM3 hr he hs0 hv
    have hK' := hK _ hext wsW _ hvW (hlay _ _ _ hl)
    obtain ⟨Rc, Rrest, hRs', ρf, ηf, c, hCE, hrid, hE, hT, hTv, ⟨hFI, hRet, hHeld⟩, hpw⟩ := hK'
    have hb := Lv.hbN hM3 hbb
    have hmF0 := Lv.merge_okCE hM3 hbb hr he hs
    have hmCE : MergeOKQ (L.cpM b η' ηW) (L.mg b) (L.σ' b) (CE ηf) (CE η') := hCE ▸ hmF0
    have hmF : MergeOKQ (L.cpM b η' ηW) (L.mg b) (L.σ' b) ηf (reB ηf η') := MergeOKQ.ofCE hmCE rfl
    have hrels : ∀ k S vs, ηf.rels k S vs → (reB ηf η').rels k S (vs.map (rl (L.mg b))) := fun k S vs h =>
      VR_merge (ηf.wit k) (fun _ => 0) (CE ηf) (CE η') S vs hmCE (RelsSound_CE ηf)
        (fun _ _ _ h => (h : False).elim) (fun _ _ _ h => (h : False).elim) (((hE.2.1 k).2.1 _ S vs).1 h)
    have hurels : ∀ k S vs, ηf.urels k S vs → (reB ηf η').urels k S (vs.map (rl (L.mg b))) := fun k S vs h =>
      VR_merge (ηf.wit k) (fun _ => 0) (CE ηf.unsee) (CE η'.unsee) S vs hmCE.unsee (RelsSound_CE ηf.unsee)
        (fun _ _ _ h => (h : False).elim) (fun _ _ _ h => (h : False).elim) (((hE.2.1 k).2.2 _ S vs).1 h)
    have hrrs : ∀ k S vs Y, ηf.rrs k S vs Y → (reB ηf η').rrs k S (vs.map (rl (L.mg b))) (Res.sw (L.σ' b) Y) :=
      fun k S vs Y h =>
        VRR_merge (ηf.wit k) (fun _ => 0) (CE ηf) (CE η') S vs Y hmCE (RRSound_CE ηf)
          (fun _ _ _ _ h => (h : False).elim) (fun _ _ _ _ h => (h : False).elim) (((hE.2.2 k).1 _ S vs Y).1 h)
    have hurrs : ∀ k S vs Y, ηf.urrs k S vs Y →
        (reB ηf η').urrs k S (vs.map (rl (L.mg b))) (Res.sw (L.σ' b) Y) := fun k S vs Y h =>
      VRR_merge (ηf.wit k) (fun _ => 0) (CE ηf.unsee) (CE η'.unsee) S vs Y hmCE.unsee (RRSound_CE ηf.unsee)
        (fun _ _ _ _ h => (h : False).elim) (fun _ _ _ _ h => (h : False).elim) (((hE.2.2 k).2 _ S vs Y).1 h)
    have hfix : ∀ (vars : List (String × Ty × Bool)) y e, vars.find? (·.1 == y) = some e → y ≠ f.x →
        ∀ rt ws', lookupE f.env y = some (rt, ws') → ws'.map (rl (L.mg b)) = ws' := by
      intro vars y e _ _ rt ws' hl'
      obtain ⟨e', he', hws⟩ := lookupE_mem hl'
      refine map_rl_fix ws' (fun w hw a g hv' => Lv.mg_low hM3 hbb ?_)
      exact hStk f List.mem_cons_self e' he' w (hws ▸ hw) a g hv'
    have hprog : η'.prog = p := he.2.2.1.trans (hr.prog.symm.trans hp)
    refine ⟨Rc, Rrest, hRs', ρf, reB ηf η', c, rfl, rfl, EnvOKB_reB hE.2.1 hprog, hT.wit rfl, hTv, ⟨?_, ?_, ?_⟩,
      hpw.1, hpw.2⟩
    · obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hFI
      have hv2 := VarsOK_merge hmF (RelsSound.of_Coh hE.2.1) hrels hurels (hfix c.vars) h2
      rw [hback] at hv2
      exact ⟨h1, hv2, fun _ _ _ _ _ _ => trivial, h4, h5, h6, h7, h8, h9, h10, h11⟩
    · have hM' : (Lv.next hM3 hbb).c₀ + 3 * (rest.length + 1) ≤ P.M := by
        show L.c₀ + 3 + 3 * (rest.length + 1) ≤ P.M
        simp only [List.length_cons] at hM; omega
      have hRs2 : RsSup P (Rc + Rrest) := hRs' ▸ hRs
      exact ih (Lv.next hM3 hbb) ηf (reB ηf η') ρf f.σs c.ret Rrest hM'
        (Lv.relW_next hM3 hbb hr he hs hCE hE.2.1 hrid) hE.1
        (fun f' hf' => hStk f' (List.mem_cons_of_mem _ hf')) (Lv.RsSup.right hM3 hbb hRs2) hRet
    · have hh := HeldOK_merge hmF (RRSound.of_CohR hE.2.2) hrrs hurrs (hfix c.vars) hHeld
      have hRs2 : RsSup P (Rc + Rrest) := hRs' ▸ hRs
      rw [hback, Res.sw_add, Res.sw_comp (Lv.«τ'σ'» hM3 hb), Lv.sw_fix hM3 hbb (Lv.RsSup.left hM3 hbb hRs2)] at hh
      exact hh

end TermSound.Flat
