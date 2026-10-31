import WeakCore.StackLevelZero
import WeakCore.VRLift
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound
open FlatAnchor (RelsSound_CE)

/-! **StackResFree** (plan (A)): the resource-free twin of F4, giving `ContE` (W `RetOK` → ♭ `RetOKB`).
Same premises as `f4` ({hSup}); same `gc` relabel (`VR_liftTop`, twin of `VRR_liftTop`).
Local mirrors: `RetOKBs`/`FInvBs`/`ResumeBs` mirror ♭ `RetOKB`/`FInvB`/`ResumeB` with the returned env restricted to
`Sup` (they unfold to the ♭ defs).  The ♭ partner `reBE` carries the frame's `rid` (resource-free
frames record no rid). -/

section mirrorE
variable (Sup : TEnv → Prop)

/-- Local mirror: `RetOKB` at supply envs only. -/
def RetOKBs (lb n i : Nat) (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (ret : Ty) (K : TEnv → List Word → Prop) : Prop :=
  ∀ η', ExtB η η' → Sup η' → ∀ ws, (VRF False) ρ η' ret (shp (close σs ret)) ws → Lay σs ret (close σs ret) ws →
    K (CE η') ws

/-- Local mirror of `FInvB`. -/
def FInvBs (lb n i : Nat) (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (K : TEnv → List Word → Prop) (cx : Cx) (env : Env) : Prop :=
  Sat cx.facts ρ ∧ VarsOKB ρ η σs cx.vars env ∧ RetOKBs Sup lb n i ρ η σs cx.ret K ∧ WitL σs η.wit cx.opq ∧
    cx.ke.length ≤ σs.length ∧ KindsOK cx.ke σs ∧ WitAF η ∧ WitSh cx.ke η ∧ WitC cx.ke η ∧ WitN cx.ke η ∧
    WitR cx.ke η

/-- Local mirror of `ResumeB`. -/
def ResumeBs (lb n i : Nat) (p : Prog) : List Frame → TEnv → List Word → Prop
  | [], _, _ => True
  | f :: rest, E, ws => ∃ ρ η c, CE η = E ∧ EnvOKB p η ∧ Typed p c f.body ∧ TvOK c ∧
      FInvBs Sup lb n i ρ η f.σs (ResumeBs lb n i p rest) c ((f.x, f.ty, ws) :: f.env) ∧
      (∀ (f' : Frame) (rest' : List Frame), rest = f' :: rest' → ∀ ws,
        TermPtrRts.pubWords f'.ty ws = TermPtrRts.pubWords (close f.σs c.ret) ws) ∧
      DyFr p annNew (progTgts p) η f.σs f.body
end mirrorE

/-- The ♭ partner for resource-free frames: `reB` with the frame's own `rid`. -/
def reBE (ηf η : TEnv) : TEnv := { reB ηf η with rid := ηf.rid }

theorem EnvOKB_reBE {p : Prog} {ηf η : TEnv} (hc : Coh ηf) (hp : η.prog = p) : EnvOKB p (reBE ηf η) :=
  EnvOKB_reB (ηf := ηf) (η := η) hc hp

namespace Lv
variable {P : Plan} {L : Lv P} {b : Nat}

section
variable (hM : L.c₀ + 3 ≤ P.M) (hbb : L.bnd ≤ b)
include hM hbb
end

/-- **lift_stepE** (twin of `lift_step`): one ♭ resource-free return lifts to W's `η″` by the same relabel. -/
theorem lift_stepE (hM : L.c₀ + 3 ≤ P.M) {ηW ηB η' : TEnv} {b₀ : Nat} (hr : RelW L ηW ηB)
    (he : ExtB ηB η') (hs0 : FreshSup P b₀ η') {ρ : Nat → Nat} {t : Ty} {rt : Shp} {ws : List Word}
    (hv : (VRF False) ρ η' t rt ws) :
    ∃ b, ∃ hbb : L.bnd ≤ b, FreshSup P b η' ∧ ∃ wsW, Ext ηW (L.etaW b η' ηW) ∧
      VR ρ (L.etaW b η' ηW) t rt wsW ∧ wsW.map (rl (L.mg b)) = ws ∧
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
  have hB : CohBW η' := he.1
  have hW : Coh (L.etaW b η' ηW) := hext.1
  have hsc : ∀ l, CpO η' l → L.σ' b l ≠ L.cpy b l := by
    rintro l ⟨c, hc, -⟩ e
    have hnt : ¬ P.Tail b l := fun hl => by rw [hs.sto l hl] at hc; cases hc
    have : l = L.cpy b l := by
      have h2 : L.τ' b (L.σ' b l) = L.τ' b (L.cpy b l) := congrArg _ e
      rw [«τ'σ'» hM hb, «τ'_cpy» hM hb] at h2
      exact h2
    exact hnt (this ▸ tail_cpy hM hb l)
  have hbc : ∀ l k, CpO η' l → L.bvar b l k ≠ L.cpy b l := fun l k _ e => cpy_ne_bvar hM hb l l k e.symm
  have hv' := VR_liftTop hsc hbc hm hci hB hW hv
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

/-- **StackResFree** (stack induction, resource-free): W's return continuation at a level-`L` caller env gives the ♭ one
(local mirror) at its partner, for every stack. -/
theorem f4E {p : Prog} {P : Plan} {Sup : TEnv → Prop}
    (hSup : ∀ η, Sup η → ∃ b, FreshSup P b η) :
    ∀ (stack : List Frame) (L : Lv P) (ηW ηB : TEnv) (ρ : Nat → Nat) (σs : List Ty) (ret : Ty),
      L.c₀ + 3 * (stack.length + 1) ≤ P.M → RelW L ηW ηB → ηW.prog = p → StkLt P stack →
      RetOK ρ ηW σs ret (Resume p stack) → RetOKBs Sup glb gnum gi ρ ηB σs ret (ResumeBs Sup glb gnum gi p stack) := by
  intro stack
  induction stack with
  | nil =>
    intro L ηW ηB ρ σs ret hM hr hp hStk hK η' he hsup ws hv hl
    trivial
  | cons f rest ih =>
    intro L ηW ηB ρ σs ret hM hr hp hStk hK η' he hsup ws hv hl
    have hM3 : L.c₀ + 3 ≤ P.M := by simp only [List.length_cons] at hM; omega
    obtain ⟨b₀, hs0⟩ := hSup η' hsup
    obtain ⟨b, hbb, hs, wsW, hext, hvW, hback, hlay⟩ := Lv.lift_stepE hM3 hr he hs0 hv
    have hK' := hK _ hext wsW hvW (hlay _ _ _ hl)
    obtain ⟨ρf, ηf, c, hCE, hE, hT, hTv, ⟨h1, h2, hRet, h4, h5, h6, h7, h8, h9, h10, h11⟩, hpw⟩ := hK'
    have hb := Lv.hbN hM3 hbb
    have hmF0 := Lv.merge_okCE hM3 hbb hr he hs
    have hmCE : MergeOKQ (L.cpM b η' ηW) (L.mg b) (L.σ' b) (CE ηf) (CE η') := hCE ▸ hmF0
    have hmF : MergeOKQ (L.cpM b η' ηW) (L.mg b) (L.σ' b) ηf (reBE ηf η') := MergeOKQ.ofCE hmCE rfl
    have hrels : ∀ k S vs, ηf.rels k S vs → (reBE ηf η').rels k S (vs.map (rl (L.mg b))) := fun k S vs h =>
      VR_merge (ηf.wit k) (fun _ => 0) (CE ηf) (CE η') S vs hmCE (RelsSound_CE ηf)
        (fun _ _ _ h => (h : False).elim) (fun _ _ _ h => (h : False).elim) (((hE.2.1 k).2.1 _ S vs).1 h)
    have hurels : ∀ k S vs, ηf.urels k S vs → (reBE ηf η').urels k S (vs.map (rl (L.mg b))) := fun k S vs h =>
      VR_merge (ηf.wit k) (fun _ => 0) (CE ηf.unsee) (CE η'.unsee) S vs hmCE.unsee (RelsSound_CE ηf.unsee)
        (fun _ _ _ h => (h : False).elim) (fun _ _ _ h => (h : False).elim) (((hE.2.1 k).2.2 _ S vs).1 h)
    have hfix : ∀ (vars : List (String × Ty × Bool)) y e, vars.find? (·.1 == y) = some e → y ≠ f.x →
        ∀ rt ws', lookupE f.env y = some (rt, ws') → ws'.map (rl (L.mg b)) = ws' := by
      intro vars y e _ _ rt ws' hl'
      obtain ⟨e', he', hws⟩ := lookupE_mem hl'
      refine map_rl_fix ws' (fun w hw a g hv' => Lv.mg_low hM3 hbb ?_)
      exact hStk f List.mem_cons_self e' he' w (hws ▸ hw) a g hv'
    have hprog : η'.prog = p := he.2.2.1.trans (hr.prog.symm.trans hp)
    refine ⟨ρf, reBE ηf η', c, rfl, EnvOKB_reBE hE.2.1 hprog, hT, hTv, ⟨h1, ?_, ?_, h4, h5, h6, h7, h8, h9, h10, h11⟩,
      hpw.1, hpw.2⟩
    · have hv2 := VarsOK_merge hmF (RelsSound.of_Coh hE.2.1) hrels hurels (hfix c.vars) h2
      rw [hback] at hv2
      exact hv2
    · have hM' : (Lv.next hM3 hbb).c₀ + 3 * (rest.length + 1) ≤ P.M := by
        show L.c₀ + 3 + 3 * (rest.length + 1) ≤ P.M
        simp only [List.length_cons] at hM; omega
      exact ih (Lv.next hM3 hbb) ηf (reBE ηf η') ρf f.σs c.ret hM'
        (Lv.relW_nextR hM3 hbb hr he hs hCE hE.2.1 ηf.rid (Nat.le_refl _)) hE.1
        (fun f' hf' => hStk f' (List.mem_cons_of_mem _ hf')) hRet

/-- **Level 0, ContE** (the seed's instance; mirror form, unfolded in `ContIV`). -/
theorem contE_f4 {p : Prog} {P : Plan} {Sup : TEnv → Prop}
    (hSup : ∀ η, Sup η → ∃ b, FreshSup P b η)
    {stack : List Frame} {σs : List Ty} {E : TEnv}
    (hM : 3 * (stack.length + 1) ≤ P.M) (hStk : StkLt P stack) (hbl : TailBlank P E) :
    ∀ (ρ : Nat → Nat) (η : TEnv) (cx : Cx), CE η = E → EnvOK p η →
      RetOK ρ η σs cx.ret (Resume p stack) →
      RetOKBs Sup glb gnum gi ρ (FlatAnchor.flat η) σs cx.ret (ResumeBs Sup glb gnum gi p stack) := by
  intro ρ η cx hCE hE hK
  subst hCE
  have hM0 : (Lv.id0 P).c₀ + 3 * (stack.length + 1) ≤ P.M := by show 0 + _ ≤ _; omega
  exact f4E hSup stack (Lv.id0 P) η (FlatAnchor.flat η) ρ σs cx.ret hM0 (relW_id0 hE.2.1 hbl) hE.1 hStk hK

end TermSound.Flat
