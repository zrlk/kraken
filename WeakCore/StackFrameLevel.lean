import WeakCore.EtaD
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! **StackFrameLevel**: the frame partner of one stack level and the F4 invariant at the next level.

W's continuation is fed at `η″ = L.etaW b η ηW` and returns a W frame env `ηf` with `CE ηf = CE η″`.  Its ♭
partner `reB ηf η` has `η`'s view (`CE`, `rid`) and `ηf`'s witnesses, with the relations re-read flatly (as `flat`).
`relW_next`: the pair `(ηf, reB ηf η)` satisfies the F4 invariant `RelW` at `L.next`. -/

/-- The ♭ partner of a W frame env `ηf` at the ♭ return env `η`. -/
def reB (ηf η : TEnv) : TEnv :=
  { rels := fun k S ws => (VRF False) (fun _ => 0) (CE η) (ηf.wit k) S ws
    urels := fun k S ws => (VRF False) (fun _ => 0) (CE η.unsee) (ηf.wit k) S ws
    wit := ηf.wit, prog := η.prog, sto := η.sto, tid := η.tid, ini := η.ini, rini := η.rini, pfr := η.pfr,
    seen := η.seen, box := η.box, rid := η.rid
    rrs := fun k S ws R => VRRB (fun _ => 0) (CE η) (ηf.wit k) S ws R
    urrs := fun k S ws R => VRRB (fun _ => 0) (CE η.unsee) (ηf.wit k) S ws R
    fp := η.fp }

theorem CE_reB (ηf η : TEnv) : CE (reB ηf η) = CE η := rfl
theorem CE_reB_unsee (ηf η : TEnv) : CE (reB ηf η).unsee = CE η.unsee := rfl

theorem EnvOKB_reB {p : Prog} {ηf η : TEnv} (hc : Coh ηf) (hp : η.prog = p) : EnvOKB p (reB ηf η) := by
  refine ⟨hp, fun k => ⟨(hc k).1, fun ρ' S ws => ?_, fun ρ' S ws => ?_⟩, fun k => ⟨fun ρ' S ws X => ?_,
    fun ρ' S ws X => ?_⟩⟩
  · exact VR_cloB (hc k).1 _ _ S ws
  · exact VR_cloB (η := η.unsee) (hc k).1 _ _ S ws
  · exact VRR_cloB (hc k).1 _ _ S ws X
  · exact VRR_cloB (η := η.unsee) (hc k).1 _ _ S ws X

theorem FreshSup.mono {P : Plan} {b b' : Nat} {η : TEnv} (h : FreshSup P b η) (hb : b ≤ b') : FreshSup P b' η :=
  ⟨fun l hl => h.sto l (Lv.Tail_mono (P := P) hb hl), fun l hl => h.box l (Lv.Tail_mono (P := P) hb hl),
    fun l hl => h.ini l (Lv.Tail_mono (P := P) hb hl), fun l hl => h.rini l (Lv.Tail_mono (P := P) hb hl),
    fun l hl => h.pfr l (Lv.Tail_mono (P := P) hb hl), fun l hl => h.seen l (Lv.Tail_mono (P := P) hb hl),
    fun x B hx w hw a g hv ht => h.pay x B hx w hw a g hv (Lv.Tail_mono (P := P) hb ht)⟩

/-- A loc word of a per-position relabel comes from a loc word of the original. -/
theorem mem_rlI_loc : ∀ (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (ws : List Word) (w : Word),
    w ∈ rlI G ws → ∀ a g, w.val = .loc a g →
      ∃ i w₀ a₀, w₀ ∈ ws ∧ w₀.val = .loc a₀ g ∧ a.label = G i a₀.label
  | _, [], w, hw, _, _, _ => by simp [rlI] at hw
  | G, w₀ :: ws, w, hw, a, g, hv => by
    simp only [rlI, List.mem_cons] at hw
    rcases hw with rfl | hw
    · cases e : w₀.val with
      | loc a₀ g₀ =>
        simp only [rl, rlv, e] at hv
        cases hv
        exact ⟨0, w₀, a₀, List.mem_cons_self, e, rfl⟩
      | _ => simp [rl, rlv, e] at hv
    · obtain ⟨i, w₁, a₁, h1, h2, h3⟩ := mem_rlI_loc (fun i => G (i + 1)) ws w hw a g hv
      exact ⟨i + 1, w₁, a₁, List.mem_cons_of_mem _ h1, h2, h3⟩

theorem mem_map_rl_loc {f : WeakMem.AllocLabel → WeakMem.AllocLabel} {ws : List Word} {w : Word}
    (hw : w ∈ ws.map (rl f)) {a : WeakMem.Address} {g : Nat} (hv : w.val = .loc a g) :
    ∃ w₀ a₀, w₀ ∈ ws ∧ w₀.val = .loc a₀ g ∧ a.label = f a₀.label := by
  obtain ⟨w₀, h0, rfl⟩ := List.mem_map.1 hw
  cases e : w₀.val with
  | loc a₀ g₀ =>
    simp only [rl, rlv, e] at hv
    cases hv
    exact ⟨w₀, a₀, h0, e, rfl⟩
  | _ => simp [rl, rlv, e] at hv

theorem PCode.dec_range (σ cpy : WeakMem.AllocLabel → WeakMem.AllocLabel) (bv : Nat → Nat → WeakMem.AllocLabel)
    (k j : Nat) : PCode.dec σ cpy bv k j = σ ∨ PCode.dec σ cpy bv k j = cpy ∨
      ∃ k', PCode.dec σ cpy bv k j = fun y => bv y k' := by
  unfold PCode.dec
  split
  · rename_i e _
    rcases e with _ | _ | e
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
  · exact Or.inl rfl

namespace Lv
variable {P : Plan} {L : Lv P} {b : Nat}

section
variable (hM : L.c₀ + 3 ≤ P.M) (hbb : L.bnd ≤ b)
include hM hbb

/-- Off the next level's old labels: not old, not a new copy, not a new variant. -/
theorem gen_of {m : WeakMem.AllocLabel} (hn : ¬ (next hM hbb).Old m) :
    ¬ L.Old m ∧ (¬ ∃ l, m = L.cpy b l) ∧ ¬ ∃ p : Nat × Nat, m = L.bvar b p.1 p.2 := by
  refine ⟨fun ho => ?_, fun h => hn (Or.inl (Or.inr h)), fun ⟨p, e⟩ => hn (Or.inr (Or.inr ⟨p.1, p.2, e⟩))⟩
  rcases ho with h | h
  · exact hn (Or.inl (Or.inl h))
  · exact hn (Or.inr (Or.inl h))

/-- Outside the used columns of the next level: generic, and fixed by `τ′`. -/
theorem fr_gen {m : WeakMem.AllocLabel} (hu : ¬ P.Used (L.c₀ + 3) m) :
    ¬ L.Old m ∧ (¬ ∃ l, m = L.cpy b l) ∧ ¬ ∃ p : Nat × Nat, m = L.bvar b p.1 p.2 := by
  have hb := hbN hM hbb
  refine ⟨fun ho => hu (Plan.Used_mono (by omega) (Old_Used ho)), fun ⟨l, e⟩ => hu (e ▸ cpy_Used3 hM hb l),
    fun ⟨p, e⟩ => hu (e ▸ bvar_Used3 hM hb p.1 p.2)⟩

theorem cls_gen' {α : Type} {m : WeakMem.AllocLabel}
    (hg : ¬ L.Old m ∧ (¬ ∃ l, m = L.cpy b l) ∧ ¬ ∃ p : Nat × Nat, m = L.bvar b p.1 p.2)
    (fc : WeakMem.AllocLabel → α) (fv : Nat → Nat → α) (fw fb : WeakMem.AllocLabel → α) :
    L.cls b m fc fv (L.oth b fw fb) = fb (L.τ' b m) := by
  rw [cls_gen L b hg.2.1 hg.2.2, oth_new L b hg.1]

/-- A ♭ label off the tail is not sent by `σ′` onto an old label of the next level. -/
theorem not_old_img {a : WeakMem.AllocLabel} (ha : ¬ P.Tail b a) : ¬ (next hM hbb).Old (L.σ' b a) := by
  have hb := hbN hM hbb
  have h2 : ¬ L.Old (L.σ' b a) := by
    intro ho
    have : a = L.mv b (L.σ' b a) := («τ'σ'» hM hb a).symm.trans («τ'_old» hM hb ho)
    exact ha (this ▸ tail_mv hM hb _)
  rintro ((h | ⟨l, e⟩) | (h | ⟨x, k, e⟩))
  · exact h2 (Or.inl h)
  · have : a = L.cpy b l := by rw [← «τ'σ'» hM hb a, e, «τ'_cpy» hM hb]
    exact ha (this ▸ tail_cpy hM hb l)
  · exact h2 (Or.inr h)
  · have : a = L.bvar b x k := by rw [← «τ'σ'» hM hb a, e, «τ'_bvar» hM hb]
    exact ha (this ▸ tail_bvar hM hb x k)

/-- The image of a ♭ payload label is old, used, or off the tail at the next level. -/
theorem img_opay {a : WeakMem.AllocLabel} (ha : ¬ P.Tail b a) :
    (next hM hbb).Old (L.σ' b a) ∨ ¬ P.Fresh (L.c₀ + 3) (L.σ' b a) ∨ ¬ P.Tail b (L.σ' b a) := by
  have hb := hbN hM hbb
  rcases Classical.em (P.Used (L.c₀ + 3) (L.σ' b a)) with hu | hu
  · exact Or.inr (Or.inl (fun hf => Plan.not_Used_of_Fresh hf hu))
  · have e := «τ'_fix» hM hb hu
    rw [«τ'σ'» hM hb] at e
    exact Or.inr (Or.inr (e ▸ ha))

end

section
variable (hM : L.c₀ + 3 ≤ P.M) (hbb : L.bnd ≤ b) {ηW ηB η ηf : TEnv}
include hM hbb

theorem cpM_of {m : WeakMem.AllocLabel} {c' : Cell} (ho : (next hM hbb).Old m)
    (h : L.stoE b η ηW m = some c') : L.cpM b η ηW m := by
  have hb := hbN hM hbb
  rcases ho with (h1 | ⟨l, e⟩) | (h1 | ⟨x, k, e⟩)
  · exact ⟨Or.inl (Or.inl h1), c', h⟩
  · exact ⟨Or.inr ⟨l, e⟩, c', h⟩
  · exact ⟨Or.inl (Or.inr h1), c', h⟩
  · subst e; unfold stoE at h; rw [cls_bvar hM hb] at h; cases h

/-- **relW_next**: the frame env and its ♭ partner satisfy the F4 invariant at the next level. -/
theorem relW_nextR (hr : RelW L ηW ηB) (he : ExtB ηB η) (hs : FreshSup P b η)
    (hCE : CE ηf = CE (L.etaW b η ηW)) (hc : Coh ηf) (r : Nat) (hrid : ηf.rid ≤ r) :
    RelW (next hM hbb) ηf { reB ηf η with rid := r } := by
  have hb := hbN hM hbb
  have esto : ηf.sto = L.stoE b η ηW := congrArg TEnv.sto hCE
  have eini : ηf.ini = L.iniE b η ηW := congrArg TEnv.ini hCE
  have erini : ηf.rini = L.riniE b η ηW := congrArg TEnv.rini hCE
  have epfr : ηf.pfr = L.pfrE b η ηW := congrArg TEnv.pfr hCE
  have eseen : ηf.seen = L.seenE b η ηW := congrArg TEnv.seen hCE
  have ebox : ηf.box = L.boxE b η ηW := congrArg TEnv.box hCE
  have eprog : ηf.prog = ηW.prog := by have h := congrArg TEnv.prog hCE; exact h
  have etid : ηf.tid = ηW.tid := by have h := congrArg TEnv.tid hCE; exact h
  have hmg : MergeOKQ (L.cpM b η ηW) (L.mg b) (L.σ' b) (CE ηf) (CE η) := hCE ▸ merge_okCE hM hbb hr he hs
  have hEp : η.prog = ηB.prog := he.2.2.1
  have hEt : η.tid = ηB.tid := he.2.2.2.1
  have ncp : ∀ m, ηf.sto m = none → ¬ L.cpM b η ηW m := fun m hn ⟨_, c, hc'⟩ => by
    rw [← esto, hn] at hc'; cases hc'
  refine
    { coh := hc
      fsto := fun m hf ht => ?_, fbox := fun m hf ht => ?_, fini := fun m hf ht => ?_,
      frini := fun m hf ht => ?_, fpfr := fun m hf ht => ?_, fseen := fun m hf ht => ?_
      sto := fun m c hn h => ?_, ini := fun m hn => ?_, rini := fun m hn => ?_, pfr := fun m q hn h => ?_,
      seen := fun m hn h => ?_, box := fun m B hn h => ?_
      pay := fun x B hx w hw a g hv => not_old_img hM hbb (hs.pay x B hx w hw a g hv)
      rid := hrid
      wit := rfl
      prog := by rw [eprog]; exact hr.prog.trans hEp.symm
      tid := by rw [etid]; exact hr.tid.trans hEt.symm
      vsto := fun m hm => ?_
      ocl := fun m c' ho h => hmg.cl m c' (cpM_of hM hbb ho (esto ▸ h)) h
      oinil := fun m c' ho h => hmg.inil m (cpM_of hM hbb ho (esto ▸ h))
      orinil := fun m c' ho h => hmg.rinil m (cpM_of hM hbb ho (esto ▸ h))
      opfrl := fun m c' ho h => hmg.pfrl m (cpM_of hM hbb ho (esto ▸ h))
      opfrc := fun m c' ho h => hmg.pfrc m (cpM_of hM hbb ho (esto ▸ h))
      oini := fun m ho hn => hmg.ini m (ncp m hn)
      orini := fun m ho hn => hmg.rini m (ncp m hn)
      opfr := fun m q ho hn h => hmg.pfr m q (ncp m hn) h
      oseen := fun m ho hn h => hmg.seen m (ncp m hn) h
      obox := fun m B ho h => hmg.box m B h
      opay := fun m B ho h w hw a g hv => ?_ }
  -- the untouched columns of the next level
  · have hg := fr_gen hM hbb (Plan.not_Used_of_Fresh hf)
    rw [esto]; unfold stoE; rw [cls_gen' hM hbb hg, «τ'_fix» hM hb (Plan.not_Used_of_Fresh hf)]
    exact hs.sto m ht
  · have hg := fr_gen hM hbb (Plan.not_Used_of_Fresh hf)
    rw [ebox]; unfold boxE; rw [cls_gen' hM hbb hg, «τ'_fix» hM hb (Plan.not_Used_of_Fresh hf), hs.box m ht]
    rfl
  · have hg := fr_gen hM hbb (Plan.not_Used_of_Fresh hf)
    rw [eini]; unfold iniE; rw [cls_gen' hM hbb hg, «τ'_fix» hM hb (Plan.not_Used_of_Fresh hf)]
    exact hs.ini m ht
  · have hg := fr_gen hM hbb (Plan.not_Used_of_Fresh hf)
    rw [erini]; unfold riniE; rw [cls_gen' hM hbb hg, «τ'_fix» hM hb (Plan.not_Used_of_Fresh hf)]
    exact hs.rini m ht
  · have hg := fr_gen hM hbb (Plan.not_Used_of_Fresh hf)
    rw [epfr]; unfold pfrE; rw [cls_gen' hM hbb hg, «τ'_fix» hM hb (Plan.not_Used_of_Fresh hf)]
    exact hs.pfr m ht
  · have hg := fr_gen hM hbb (Plan.not_Used_of_Fresh hf)
    rw [eseen]; unfold seenE; rw [cls_gen' hM hbb hg, «τ'_fix» hM hb (Plan.not_Used_of_Fresh hf)]
    exact hs.seen m ht
  -- generic labels: `η′` moved by `σ′`
  · rw [esto] at h; unfold stoE at h; rw [cls_gen' hM hbb (gen_of hM hbb hn)] at h; exact h
  · show ηf.ini m ≤ η.ini (L.τ' b m)
    rw [eini]; unfold iniE; rw [cls_gen' hM hbb (gen_of hM hbb hn)]; exact Nat.le_refl _
  · show ηf.rini m ≤ η.rini (L.τ' b m)
    rw [erini]; unfold riniE; rw [cls_gen' hM hbb (gen_of hM hbb hn)]; exact Nat.le_refl _
  · rw [epfr] at h; unfold pfrE at h; rw [cls_gen' hM hbb (gen_of hM hbb hn)] at h; exact h
  · rw [eseen] at h; unfold seenE at h; rw [cls_gen' hM hbb (gen_of hM hbb hn)] at h; exact h
  · rw [ebox] at h; unfold boxE at h; rw [cls_gen' hM hbb (gen_of hM hbb hn)] at h
    cases e : η.box (L.τ' b m) with
    | none => rw [e] at h; cases h
    | some B' => rw [e] at h; cases h; exact ⟨B', e, rfl⟩
  -- vsto
  · rw [esto]; unfold stoE
    rcases hm with h1 | ⟨x, k, rfl⟩
    · rw [cls_old hM hb (Or.inr h1)]; exact hr.vsto m h1
    · rw [cls_bvar hM hb]
  -- opay
  · rw [ebox] at h; unfold boxE at h
    have hold : ∀ (ho' : L.Old m), (next hM hbb).Old a.label ∨ ¬ P.Fresh (L.c₀ + 3) a.label ∨ ¬ P.Tail b a.label :=
      fun ho' => by
        rw [cls_old hM hb ho'] at h
        rcases hr.opay m B ho' h w hw a g hv with h1 | h1 | h1
        · rcases h1 with h1 | h1
          · exact Or.inl (Or.inl (Or.inl h1))
          · exact Or.inl (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inl (fun hf => h1 (Plan.Fresh_anti (by omega) hf)))
        · exact Or.inr (Or.inr (fun ht => h1 (Tail_mono hbb ht)))
    rcases ho with (h1 | ⟨l, rfl⟩) | (h1 | ⟨x, k, rfl⟩)
    · exact hold (Or.inl h1)
    · rw [cls_cpy hM hb] at h
      cases e : η.box l with
      | none => rw [e] at h; cases h
      | some B₀ =>
        rw [e] at h; cases h
        obtain ⟨w₀, a₀, h0, h1, h2⟩ := mem_map_rl_loc hw hv
        rw [h2]; exact img_opay hM hbb (hs.pay l B₀ e w₀ h0 a₀ g h1)
    · exact hold (Or.inr h1)
    · rw [cls_bvar hM hb] at h
      cases e : η.box x with
      | none => rw [e] at h; cases h
      | some B₀ =>
        rw [e] at h; cases h
        obtain ⟨i, w₀, a₀, h0, h1, h2⟩ := mem_rlI_loc _ _ w hw a g hv
        have ha₀ := hs.pay x B₀ e w₀ h0 a₀ g h1
        rw [h2]
        rcases PCode.dec_range (L.σ' b) (L.cpy b) (L.bvar b) k i with hd | hd | ⟨k', hd⟩ <;> rw [hd]
        · exact img_opay hM hbb ha₀
        · exact Or.inl (Or.inl (Or.inr ⟨_, rfl⟩))
        · exact Or.inl (Or.inr (Or.inr ⟨_, _, rfl⟩))


/-- **relW_next**: the frame env and its ♭ partner satisfy the F4 invariant at the next level. -/
theorem relW_next (hr : RelW L ηW ηB) (he : ExtB ηB η) (hs : FreshSup P b η)
    (hCE : CE ηf = CE (L.etaW b η ηW)) (hc : Coh ηf) (hrid : ηf.rid = η.rid) :
    RelW (next hM hbb) ηf (reB ηf η) :=
  relW_nextR hM hbb hr he hs hCE hc η.rid (Nat.le_of_eq hrid)

end
end Lv
end TermSound.Flat
