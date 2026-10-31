import WeakCore.EtaB
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! **EtaD**: the merge side of one stack level.

The level's merge map `mg` (W → ♭) sends a new copy row `cpy l` to `l`, a new variant `bvar x k` to `x`, an old
copy/variant (`L.Old`) to its ♭ original `L.og`, and everything else to its ♭ preimage `τ′`.  Its merge copy set
`cpM` is the copies (old or new) that carry a cell in `η″`.  `merge_ok` gives `MergeOKQ cpM mg σ′` between any W
env with the `CE` of `η″` and any ♭ env with the `CE` of `η′` (the frame env and its ♭ partner in F4).  With the
rc seed (copies' `ini` := `rc`), `inil` holds by construction: no MergeIL. -/

namespace Lv
variable {P : Plan} (L : Lv P) (b : Nat)

/-- The level's merge map (W → ♭). -/
noncomputable def mg (m : WeakMem.AllocLabel) : WeakMem.AllocLabel :=
  L.cls b m (fun l => l) (fun x _ => x) (L.oth b L.og (fun l => l))

/-- The merge's copy labels: copies (old or new) carrying a cell in `η″`. -/
def cpM (η ηW : TEnv) (m : WeakMem.AllocLabel) : Prop :=
  (L.Old m ∨ ∃ l, m = L.cpy b l) ∧ ∃ c, L.stoE b η ηW m = some c

theorem cls_gen {α : Type} {m : WeakMem.AllocLabel} (h0 : ¬ ∃ l, m = L.cpy b l)
    (h1 : ¬ ∃ p : Nat × Nat, m = L.bvar b p.1 p.2) (fc : WeakMem.AllocLabel → α) (fv : Nat → Nat → α)
    (fo : WeakMem.AllocLabel → α) : L.cls b m fc fv fo = fo m := by
  unfold cls; rw [dif_neg h0, dif_neg h1]

theorem oth_new {α : Type} {m : WeakMem.AllocLabel} (ho : ¬ L.Old m) (fw fb : WeakMem.AllocLabel → α) :
    L.oth b fw fb m = fb (L.τ' b m) := by
  unfold oth; rw [if_neg ho]

theorem kinds (m : WeakMem.AllocLabel) :
    (∃ l, m = L.cpy b l) ∨ (∃ x k, m = L.bvar b x k) ∨ L.Old m ∨
      (¬ L.Old m ∧ (¬ ∃ l, m = L.cpy b l) ∧ ¬ ∃ p : Nat × Nat, m = L.bvar b p.1 p.2) := by
  rcases Classical.em (∃ l, m = L.cpy b l) with h0 | h0
  · exact Or.inl h0
  rcases Classical.em (∃ p : Nat × Nat, m = L.bvar b p.1 p.2) with h1 | h1
  · obtain ⟨p, e⟩ := h1; exact Or.inr (Or.inl ⟨p.1, p.2, e⟩)
  rcases Classical.em (L.Old m) with ho | ho
  · exact Or.inr (Or.inr (Or.inl ho))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, h0, h1⟩))

variable {L b}
section
variable (hM : L.c₀ + 3 ≤ P.M) (hbb : L.bnd ≤ b)
include hM hbb

theorem hbN : P.N ≤ b := Nat.le_trans L.hbnd hbb

theorem mg_cpy (l : WeakMem.AllocLabel) : L.mg b (L.cpy b l) = l := cls_cpy hM (hbN hM hbb) l _ _ _
theorem mg_bvar (x k : Nat) : L.mg b (L.bvar b x k) = x := cls_bvar hM (hbN hM hbb) x k _ _ _
theorem mg_old {m : WeakMem.AllocLabel} (ho : L.Old m) : L.mg b m = L.og m := cls_old hM (hbN hM hbb) ho _ _ _ _
theorem mg_gen {m : WeakMem.AllocLabel} (ho : ¬ L.Old m) (h0 : ¬ ∃ l, m = L.cpy b l)
    (h1 : ¬ ∃ p : Nat × Nat, m = L.bvar b p.1 p.2) : L.mg b m = L.τ' b m := by
  unfold mg; rw [cls_gen L b h0 h1, oth_new L b ho]
theorem mg_σ' {a : WeakMem.AllocLabel} (ht : ¬ P.Tail b a) : L.mg b (L.σ' b a) = a :=
  cls_img hM (hbN hM hbb) a _ _ _ _ ht

/-- On the labels of an old box payload, `og` is the merge map. -/
theorem og_mg {a : WeakMem.AllocLabel} (h : L.Old a ∨ ¬ P.Fresh L.c₀ a ∨ ¬ P.Tail L.bnd a) :
    L.og a = L.mg b a := by
  rcases Classical.em (L.Old a) with ho | ho
  · exact (mg_old hM hbb ho).symm
  · have hf : ¬ (P.Fresh L.c₀ a ∧ P.Tail L.bnd a) := fun ⟨h1, h2⟩ => by
      rcases h with h | h | h
      · exact ho h
      · exact h h1
      · exact h h2
    rw [L.ogτ a ho]
    unfold mg; rw [cls_mid hM (hbN hM hbb) hbb ho hf]

theorem old_not_cpy {m : WeakMem.AllocLabel} (ho : L.Old m) : ¬ ∃ l, m = L.cpy b l :=
  fun ⟨l, e⟩ => cpy_not_Old hM (hbN hM hbb) l (e ▸ ho)

omit hM hbb in
/-- `(ws.map (rl h)).map (rl g) = ws` when `g` undoes `h` on the labels of `ws`. -/
theorem map_rl_back {g h : WeakMem.AllocLabel → WeakMem.AllocLabel} :
    ∀ (ws : List Word), (∀ w ∈ ws, ∀ a k, w.val = .loc a k → g (h a.label) = a.label) →
      (ws.map (rl h)).map (rl g) = ws
  | [], _ => rfl
  | w :: ws, hw => by
    simp only [List.map_cons]
    rw [rl_rl_back (fun a k hv => hw w List.mem_cons_self a k hv),
      map_rl_back ws (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))]

/-- A box moved by `σ′` (payload off the tail) merges back under `mg`. -/
theorem box_back {η : TEnv} (hs : FreshSup P b η) {x : WeakMem.AllocLabel} {B' : Box} (hx : η.box x = some B') :
    η.box x = some { ({ B' with pay := B'.pay.map (rl (L.σ' b)) } : Box) with
      pay := (B'.pay.map (rl (L.σ' b))).map (rl (L.mg b)) } := by
  rw [map_rl_back B'.pay (fun w hw a k hv => mg_σ' hM hbb (hs.pay x B' hx w hw a k hv))]
  exact hx


/-- `mg` agrees with `τ′` off the next level's old labels (`og′ = mg` agrees with `τ` off `Old′`). -/
theorem mg_off {a : WeakMem.AllocLabel}
    (h : ¬ ((L.cp a ∨ ∃ l, a = L.cpy b l) ∨ (L.cpb a ∨ ∃ x k, a = L.bvar b x k))) : L.mg b a = L.τ' b a := by
  refine mg_gen hM hbb ?_ ?_ ?_
  · intro ho; rcases ho with ho | ho
    · exact h (Or.inl (Or.inl ho))
    · exact h (Or.inr (Or.inl ho))
  · intro e; exact h (Or.inl (Or.inr e))
  · intro ⟨p, e⟩; exact h (Or.inr (Or.inr ⟨p.1, p.2, e⟩))

/-- The next stack level: columns `c₀+3…`, maps `σ′/τ′`, old copies/variants grown by this level's rows,
merge-back map `mg`, base bound `b`. -/
noncomputable def next : Lv P :=
  { c₀ := L.c₀ + 3, σ := L.σ' b, τ := L.τ' b,
    cp := fun m => L.cp m ∨ ∃ l, m = L.cpy b l,
    cpb := fun m => L.cpb m ∨ ∃ x k, m = L.bvar b x k,
    sl := τ'σ' hM (hbN hM hbb), sr := σ'τ' hM (hbN hM hbb),
    fix := fun _ h => σ'_fix hM (hbN hM hbb) h,
    cpU := fun m h => by
      rcases h with h | ⟨l, e⟩
      · exact Plan.Used_mono (by omega) (L.cpU m h)
      · rw [e]; exact cpy_Used3 hM (hbN hM hbb) l,
    cpbU := fun m h => by
      rcases h with h | ⟨x, k, e⟩
      · exact Plan.Used_mono (by omega) (L.cpbU m h)
      · rw [e]; exact bvar_Used3 hM (hbN hM hbb) x k,
    og := L.mg b, ogτ := fun _ h => mg_off hM hbb h,
    bnd := b, hbnd := hbN hM hbb }

theorem next_c₀ : (next hM hbb).c₀ = L.c₀ + 3 := rfl
theorem next_og : (next hM hbb).og = L.mg b := rfl
theorem next_bnd : (next hM hbb).bnd = b := rfl

end

section
variable (hM : L.c₀ + 3 ≤ P.M) (hbb : L.bnd ≤ b) {η ηW ηB : TEnv}
include hM hbb

theorem old_none {m : WeakMem.AllocLabel} (ho : L.Old m) (hn : ¬ L.cpM b η ηW m) : ηW.sto m = none := by
  cases e : ηW.sto m with
  | none => rfl
  | some c =>
    exact absurd ⟨Or.inl ho, c, by unfold stoE; rw [cls_old hM (hbN hM hbb) ho]; exact e⟩ hn

theorem cell_gen {m : WeakMem.AllocLabel} {c : Cell} (hn : ¬ L.cpM b η ηW m) (hc : L.stoE b η ηW m = some c) :
    ¬ L.Old m ∧ (¬ ∃ l, m = L.cpy b l) ∧ ¬ ∃ p : Nat × Nat, m = L.bvar b p.1 p.2 := by
  rcases kinds L b m with ⟨l, rfl⟩ | ⟨x, k, rfl⟩ | ho | hg
  · exact absurd ⟨Or.inr ⟨l, rfl⟩, c, hc⟩ hn
  · unfold stoE at hc; rw [cls_bvar hM (hbN hM hbb)] at hc; cases hc
  · exact absurd ⟨Or.inl ho, c, hc⟩ hn
  · exact hg

/-- **merge_ok** (core, at the `CE`s): `η″` merges into `η′`. -/
theorem merge_okCE (hr : RelW L ηW ηB) (he : ExtB ηB η) (hs : FreshSup P b η) :
    MergeOKQ (L.cpM b η ηW) (L.mg b) (L.σ' b) (CE (L.etaW b η ηW)) (CE η) := by
  have hb := hbN hM hbb
  obtain ⟨-, -, hEp, hEt, hEs, hEi, hEpf, hEse, hEb, -, -, hEri⟩ := he
  have hrc : ∀ x, ηB.rc x ≤ η.rc x := fun x => by
    simp only [TEnv.rc]; have := hEi x; have := hEri x; omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ηW.prog = η.prog; rw [hEp]; exact hr.prog
  · show ηW.tid = η.tid; rw [hEt]; exact hr.tid
  · -- fσ
    intro m hm
    have hn : ¬ L.cpM b η ηW m := fun h => hm (Or.inl h)
    cases e : L.stoE b η ηW m with
    | none => exact absurd (Or.inr e) hm
    | some c =>
      obtain ⟨ho, h0, h1⟩ := cell_gen hM hbb hn e
      rw [mg_gen hM hbb ho h0 h1]; exact «σ'τ'» hM hb m
  · -- σf
    intro m hm
    have hn : ¬ L.cpM b η ηW (L.σ' b m) := fun h => hm (Or.inl h)
    cases e : L.stoE b η ηW (L.σ' b m) with
    | none => exact absurd (Or.inr e) hm
    | some c =>
      obtain ⟨ho, h0, h1⟩ := cell_gen hM hbb hn e
      rw [mg_gen hM hbb ho h0 h1]; exact «τ'σ'» hM hb m
  · -- sto
    intro m c hn h
    change L.stoE b η ηW m = some c at h
    obtain ⟨ho, h0, h1⟩ := cell_gen hM hbb hn h
    show η.sto _ = some c
    rw [mg_gen hM hbb ho h0 h1]
    unfold stoE at h; rw [cls_gen L b h0 h1, oth_new L b ho] at h; exact h
  · -- ini
    intro m hn
    show L.iniE b η ηW m ≤ η.ini (L.mg b m)
    rcases kinds L b m with ⟨l, rfl⟩ | ⟨x, k, rfl⟩ | ho | ⟨ho, h0, h1⟩
    · unfold iniE; rw [cls_cpy hM hb, mg_cpy hM hbb]; simp only [TEnv.rc]; exact Nat.min_le_left _ _
    · unfold iniE; rw [cls_bvar hM hb, mg_bvar hM hbb]; exact Nat.le_refl _
    · unfold iniE; rw [cls_old hM hb ho, mg_old hM hbb ho]
      exact Nat.le_trans (hr.oini m ho (old_none hM hbb ho hn)) (hEi _)
    · unfold iniE; rw [cls_gen L b h0 h1, oth_new L b ho, mg_gen hM hbb ho h0 h1]; exact Nat.le_refl _
  · -- rini
    intro m hn
    show L.riniE b η ηW m ≤ η.rini (L.mg b m)
    rcases kinds L b m with ⟨l, rfl⟩ | ⟨x, k, rfl⟩ | ho | ⟨ho, h0, h1⟩
    · unfold riniE; rw [cls_cpy hM hb, mg_cpy hM hbb]; exact Nat.min_le_right _ _
    · unfold riniE; rw [cls_bvar hM hb, mg_bvar hM hbb]; exact Nat.le_refl _
    · unfold riniE; rw [cls_old hM hb ho, mg_old hM hbb ho]
      exact Nat.le_trans (hr.orini m ho (old_none hM hbb ho hn)) (hEri _)
    · unfold riniE; rw [cls_gen L b h0 h1, oth_new L b ho, mg_gen hM hbb ho h0 h1]; exact Nat.le_refl _
  · -- pfr
    intro m q hn h
    change L.pfrE b η ηW m = some q at h
    show η.pfr (L.mg b m) = some q
    rcases kinds L b m with ⟨l, rfl⟩ | ⟨x, k, rfl⟩ | ho | ⟨ho, h0, h1⟩
    · unfold pfrE at h; rw [cls_cpy hM hb] at h; rw [mg_cpy hM hbb]
      by_cases hp : CpO η l
      · obtain ⟨c, hc, -⟩ := id hp
        refine absurd ⟨Or.inr ⟨l, rfl⟩, { c with owner := none }, ?_⟩ hn
        unfold stoE; rw [cls_cpy hM hb, if_pos hp, hc]; rfl
      · rw [if_neg hp] at h; exact h
    · unfold pfrE at h; rw [cls_bvar hM hb] at h; rw [mg_bvar hM hbb]; exact h
    · unfold pfrE at h; rw [cls_old hM hb ho] at h; rw [mg_old hM hbb ho]
      exact hEpf _ _ (hr.opfr m q ho (old_none hM hbb ho hn) h)
    · unfold pfrE at h; rw [cls_gen L b h0 h1, oth_new L b ho] at h; rw [mg_gen hM hbb ho h0 h1]; exact h
  · -- seen
    intro m hn h
    change L.seenE b η ηW m at h
    show η.seen (L.mg b m)
    rcases kinds L b m with ⟨l, rfl⟩ | ⟨x, k, rfl⟩ | ho | ⟨ho, h0, h1⟩
    · unfold seenE at h; rw [cls_cpy hM hb] at h; exact h.elim
    · unfold seenE at h; rw [cls_bvar hM hb] at h; rw [mg_bvar hM hbb]; exact h
    · unfold seenE at h; rw [cls_old hM hb ho] at h; rw [mg_old hM hbb ho]
      exact hEse _ (hr.oseen m ho (old_none hM hbb ho hn) h)
    · unfold seenE at h; rw [cls_gen L b h0 h1, oth_new L b ho] at h; rw [mg_gen hM hbb ho h0 h1]; exact h
  · -- box
    intro m B h
    change L.boxE b η ηW m = some B at h
    show η.box (L.mg b m) = _
    rcases kinds L b m with ⟨l, rfl⟩ | ⟨x, k, rfl⟩ | ho | ⟨ho, h0, h1⟩
    · unfold boxE at h; rw [cls_cpy hM hb] at h; rw [mg_cpy hM hbb]
      cases e : η.box l with
      | none => rw [e] at h; cases h
      | some B' => rw [e] at h; cases h; exact e.symm.trans (box_back hM hbb hs e)
    · unfold boxE at h; rw [cls_bvar hM hb] at h; rw [mg_bvar hM hbb]
      cases e : η.box x with
      | none => rw [e] at h; cases h
      | some B' =>
        rw [e] at h; cases h
        rw [variant_pay_back (σ := L.σ' b) (cpy := L.cpy b) (bv := L.bvar b) (f := L.mg b) k B'.pay (fun w hw a g hv => ⟨mg_σ' hM hbb (hs.pay x B' e w hw a g hv),
          mg_cpy hM hbb a.label, fun k' => mg_bvar hM hbb a.label k'⟩)]
    · unfold boxE at h; rw [cls_old hM hb ho] at h; rw [mg_old hM hbb ho]
      rw [hEb _ _ (hr.obox m B ho h)]
      rw [map_rl_congr B.pay (fun w hw a g hv => og_mg hM hbb (hr.opay m B ho h w hw a g hv))]
    · unfold boxE at h; rw [cls_gen L b h0 h1, oth_new L b ho] at h; rw [mg_gen hM hbb ho h0 h1]
      cases e : η.box (L.τ' b m) with
      | none => rw [e] at h; cases h
      | some B' => rw [e] at h; cases h; exact e.symm.trans (box_back hM hbb hs e)
  · -- cl
    intro m c' hk h
    change L.stoE b η ηW m = some c' at h
    show ∃ c, η.sto (L.mg b m) = some c ∧ c'.ty = c.ty ∧ c'.owner = none ∧ c.owner = some η.tid
    rcases Classical.em (L.Old m) with ho | ho
    · unfold stoE at h; rw [cls_old hM hb ho] at h
      obtain ⟨c, h1, h2, h3, h4⟩ := hr.ocl m c' ho h
      refine ⟨c, ?_, h2, h3, ?_⟩
      · rw [mg_old hM hbb ho]; exact hEs _ _ h1
      · rw [hEt]; exact h4
    · obtain ⟨l, rfl⟩ := hk.1.resolve_left ho
      unfold stoE at h; rw [cls_cpy hM hb] at h; rw [mg_cpy hM hbb]
      by_cases hp : CpO η l
      · obtain ⟨c, hc, hown, -⟩ := id hp
        rw [if_pos hp, hc] at h
        cases h
        exact ⟨c, hc, rfl, rfl, hown⟩
      · rw [if_neg hp] at h; cases h
  · -- inil
    intro m hk
    show L.iniE b η ηW m ≤ η.rc (L.mg b m)
    obtain ⟨hk, c', h⟩ := hk
    rcases Classical.em (L.Old m) with ho | ho
    · have h' : ηW.sto m = some c' := by unfold stoE at h; rw [cls_old hM hb ho] at h; exact h
      unfold iniE; rw [cls_old hM hb ho, mg_old hM hbb ho]
      exact Nat.le_trans (hr.oinil m c' ho h') (hrc _)
    · obtain ⟨l, rfl⟩ := hk.resolve_left ho
      rw [mg_cpy hM hbb]
      unfold stoE at h; rw [cls_cpy hM hb] at h
      by_cases hp : CpO η l
      · unfold iniE; rw [cls_cpy hM hb]; exact Nat.le_refl _
      · rw [if_neg hp] at h; cases h
  · -- rinil
    intro m hk
    show L.riniE b η ηW m ≤ η.rc (L.mg b m)
    obtain ⟨hk, c', h⟩ := hk
    rcases Classical.em (L.Old m) with ho | ho
    · have h' : ηW.sto m = some c' := by unfold stoE at h; rw [cls_old hM hb ho] at h; exact h
      unfold riniE; rw [cls_old hM hb ho, mg_old hM hbb ho]
      exact Nat.le_trans (hr.orinil m c' ho h') (hrc _)
    · obtain ⟨l, rfl⟩ := hk.resolve_left ho
      unfold riniE; rw [cls_cpy hM hb, mg_cpy hM hbb]; exact Nat.le_refl _
  · -- pfrl
    intro m hk
    show ∃ q, η.pfr (L.mg b m) = some q
    obtain ⟨hk, c', h⟩ := hk
    rcases Classical.em (L.Old m) with ho | ho
    · have h' : ηW.sto m = some c' := by unfold stoE at h; rw [cls_old hM hb ho] at h; exact h
      obtain ⟨q, hq⟩ := hr.opfrl m c' ho h'
      rw [mg_old hM hbb ho]; exact ⟨q, hEpf _ _ hq⟩
    · obtain ⟨l, rfl⟩ := hk.resolve_left ho
      rw [mg_cpy hM hbb]
      unfold stoE at h; rw [cls_cpy hM hb] at h
      by_cases hp : CpO η l
      · obtain ⟨-, -, -, q, hq⟩ := hp; exact ⟨q, hq⟩
      · rw [if_neg hp] at h; cases h
  · -- pfrc
    intro m hk
    show ∃ q, L.pfrE b η ηW m = some q ∧ ∀ v : WeakMem.Ts, q ≤ v
    obtain ⟨hk, c', h⟩ := hk
    rcases Classical.em (L.Old m) with ho | ho
    · have h' : ηW.sto m = some c' := by unfold stoE at h; rw [cls_old hM hb ho] at h; exact h
      unfold pfrE; rw [cls_old hM hb ho]; exact hr.opfrc m c' ho h'
    · obtain ⟨l, rfl⟩ := hk.resolve_left ho
      unfold stoE at h; rw [cls_cpy hM hb] at h
      by_cases hp : CpO η l
      · unfold pfrE; rw [cls_cpy hM hb, if_pos hp]; exact ⟨0, rfl, fun v => Nat.zero_le v⟩
      · rw [if_neg hp] at h; cases h

end
end Lv

/-- `MergeOKQ` reads only the `CE` fields and the witnesses. -/
theorem MergeOKQ.ofCE {cp : WeakMem.AllocLabel → Prop} {f σ : WeakMem.AllocLabel → WeakMem.AllocLabel}
    {η₁ η₂ : TEnv} (h : MergeOKQ cp f σ (CE η₁) (CE η₂)) (hw : η₁.wit = η₂.wit) : MergeOKQ cp f σ η₁ η₂ :=
  ⟨hw, h.prog, h.tid, h.fσ, h.σf, h.sto, h.ini, h.rini, h.pfr, h.seen, h.box, h.cl, h.inil, h.rinil, h.pfrl,
    h.pfrc⟩

end TermSound.Flat
