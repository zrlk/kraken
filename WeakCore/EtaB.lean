import WeakCore.VarBox
import WeakCore.EtaA
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! **EtaB**: the W query env `η″` of one stack level, and its `LiftOKQ` from the ♭ env `η′`.

`η″ := ηW.withSto …` (W witnesses/program/thread from the caller's W env `ηW`, relations re-read by `withSto`,
so `Coh`/`CohR` are free).  Its Σ and ghosts are `η′`'s moved by the level bijection `σ′ = L.σ' b`, plus
* the cell copies `cpy l` (column `c₀`) of the owned published cells (`CpO η′ l`), owner `none`, frontier `0`,
  `ini` and `rini` seeded with `rc l` (the rc seed);
* the box variants `bvar x k` (column `c₀+2`) of every ♭ box `x` and every payload code `k`;
* at the OLD copy/variant labels (`L.Old`, the W objects of the levels below), `ηW`'s own objects (their ♭
  preimages are this level's move labels, blank in `η′`), so that `Ext ηW η″` holds.
The only property of `η′` used for the lift is the supply `FreshSup` above the base `b`. -/

/-- A progression label of index `≥ b` (the tail above the level's base). -/
def Plan.Tail (P : Plan) (b : Nat) (l : WeakMem.AllocLabel) : Prop := ∃ k, b ≤ k ∧ l = P.fl k

/-- The supply: `η` is blank on the progression tail above `b`, and its box payloads do not mention it. -/
structure FreshSup (P : Plan) (b : Nat) (η : TEnv) : Prop where
  sto : ∀ l, P.Tail b l → η.sto l = none
  box : ∀ l, P.Tail b l → η.box l = none
  ini : ∀ l, P.Tail b l → η.ini l = 0
  rini : ∀ l, P.Tail b l → η.rini l = 0
  pfr : ∀ l, P.Tail b l → η.pfr l = none
  seen : ∀ l, P.Tail b l → ¬ η.seen l
  pay : ∀ x B, η.box x = some B → ∀ w ∈ B.pay, ∀ a g, w.val = .loc a g → ¬ P.Tail b a.label

/-- The labels that get a copy: owned cells with a frontier (`LiftOKQ.cown`). -/
def CpO (η : TEnv) (l : WeakMem.AllocLabel) : Prop :=
  ∃ c, η.sto l = some c ∧ c.owner = some η.tid ∧ ∃ q, η.pfr l = some q

namespace Lv
variable {P : Plan} (L : Lv P) (b : Nat) (η ηW : TEnv)

open Classical in
/-- Classify a W label: a copy row, a variant `(x, k)`, or anything else (`fo` gets the W label). -/
noncomputable def cls {α : Type} (m : WeakMem.AllocLabel) (fc : WeakMem.AllocLabel → α) (fv : Nat → Nat → α)
    (fo : WeakMem.AllocLabel → α) : α :=
  if h : ∃ l, m = L.cpy b l then fc (Classical.choose h)
  else if h' : ∃ p : Nat × Nat, m = L.bvar b p.1 p.2 then fv (Classical.choose h').1 (Classical.choose h').2
  else fo m

open Classical in
/-- Off the new rows: the old W object (`L.Old`), else the ♭ object at the preimage. -/
noncomputable def oth {α : Type} (fw fb : WeakMem.AllocLabel → α) (m : WeakMem.AllocLabel) : α :=
  if L.Old m then fw m else fb (L.τ' b m)

open Classical in
noncomputable def stoE : WeakMem.AllocLabel → Option Cell := fun m =>
  L.cls b m (fun l => if CpO η l then (η.sto l).map (fun c => { c with owner := none }) else none)
    (fun _ _ => none) (L.oth b ηW.sto η.sto)

noncomputable def iniE : WeakMem.AllocLabel → Nat := fun m =>
  L.cls b m η.rc (fun x _ => η.ini x) (L.oth b ηW.ini η.ini)
noncomputable def riniE : WeakMem.AllocLabel → Nat := fun m =>
  L.cls b m η.rc (fun x _ => η.rini x) (L.oth b ηW.rini η.rini)
open Classical in
noncomputable def pfrE : WeakMem.AllocLabel → Option WeakMem.Ts := fun m =>
  L.cls b m (fun l => if CpO η l then some 0 else η.pfr l) (fun x _ => η.pfr x) (L.oth b ηW.pfr η.pfr)
noncomputable def seenE : WeakMem.AllocLabel → Prop := fun m =>
  L.cls b m (fun _ => False) (fun x _ => η.seen x) (L.oth b ηW.seen η.seen)
noncomputable def boxE : WeakMem.AllocLabel → Option Box := fun m =>
  L.cls b m (fun l => (η.box l).map (fun B => { B with pay := B.pay.map (rl (L.σ' b)) }))
    (fun x k => (η.box x).map (fun B => { B with pay := rlI (PCode.dec (L.σ' b) (L.cpy b) (L.bvar b) k) B.pay }))
    (L.oth b ηW.box (fun l => (η.box l).map (fun B => { B with pay := B.pay.map (rl (L.σ' b)) })))

/-- **η″** of the level, on top of the caller's W env `ηW`. -/
noncomputable def etaW : TEnv :=
  ηW.withSto (L.stoE b η ηW) (L.iniE b η ηW) (L.pfrE b η ηW) (L.seenE b η ηW) (L.boxE b η ηW) η.rid η.fp
    (L.riniE b η ηW)

variable {L b}
variable (hM : L.c₀ + 3 ≤ P.M) (hb : P.N ≤ b)
include hM hb

theorem cls_cpy {α : Type} (l : WeakMem.AllocLabel) (fc : WeakMem.AllocLabel → α) (fv : Nat → Nat → α)
    (fo : WeakMem.AllocLabel → α) : L.cls b (L.cpy b l) fc fv fo = fc l := by
  unfold cls
  have h : ∃ l', L.cpy b l = L.cpy b l' := ⟨l, rfl⟩
  rw [dif_pos h]
  exact congrArg fc (cpy_inj hM hb (Classical.choose_spec h)).symm

theorem cls_bvar {α : Type} (x k : Nat) (fc : WeakMem.AllocLabel → α) (fv : Nat → Nat → α)
    (fo : WeakMem.AllocLabel → α) : L.cls b (L.bvar b x k) fc fv fo = fv x k := by
  unfold cls
  have h0 : ¬ ∃ l, L.bvar b x k = L.cpy b l := fun ⟨l, e⟩ => cpy_ne_bvar hM hb l x k e.symm
  have h : ∃ p : Nat × Nat, L.bvar b x k = L.bvar b p.1 p.2 := ⟨(x, k), rfl⟩
  rw [dif_neg h0, dif_pos h]
  obtain ⟨e1, e2⟩ := bvar_inj hM hb (Classical.choose_spec h)
  rw [← e1, ← e2]

theorem tail_cpy (l : WeakMem.AllocLabel) : P.Tail b (L.cpy b l) := Plan.lbl_tail (Nat.le_refl b)
theorem tail_bvar (x k : Nat) : P.Tail b (L.bvar b x k) := Plan.lbl_tail (Nat.le_refl b)
theorem tail_mv (l : WeakMem.AllocLabel) : P.Tail b (L.mv b l) := Plan.lbl_tail (Nat.le_refl b)

/-- At the image of a ♭ label off the tail, `cls`/`oth` read the label itself. -/
theorem cls_img {α : Type} (l : WeakMem.AllocLabel) (fc : WeakMem.AllocLabel → α) (fv : Nat → Nat → α)
    (fw fb : WeakMem.AllocLabel → α) (hl : ¬ P.Tail b l) : L.cls b (L.σ' b l) fc fv (L.oth b fw fb) = fb l := by
  unfold cls
  have h0 : ¬ ∃ l', L.σ' b l = L.cpy b l' := by
    rintro ⟨l', e⟩
    have : l = L.cpy b l' := by rw [← «τ'σ'» hM hb l, e, «τ'_cpy» hM hb]
    exact hl (this ▸ tail_cpy hM hb l')
  have h1 : ¬ ∃ p : Nat × Nat, L.σ' b l = L.bvar b p.1 p.2 := by
    rintro ⟨p, e⟩
    have : l = L.bvar b p.1 p.2 := by rw [← «τ'σ'» hM hb l, e, «τ'_bvar» hM hb]
    exact hl (this ▸ tail_bvar hM hb p.1 p.2)
  have h2 : ¬ L.Old (L.σ' b l) := by
    intro ho
    have : l = L.mv b (L.σ' b l) := («τ'σ'» hM hb l).symm.trans («τ'_old» hM hb ho)
    exact hl (this ▸ tail_mv hM hb _)
  rw [dif_neg h0, dif_neg h1]
  unfold oth; rw [if_neg h2, «τ'σ'» hM hb]

/-- **lift_ok**: `η′` (♭, with the supply) lifts to `η″` at this level. -/
theorem lift_ok (hs : FreshSup P b η) (hw : ηW.wit = η.wit) (hp : ηW.prog = η.prog)
    (ht : ηW.tid = η.tid) :
    LiftOKQ (L.cpy b) (L.σ' b) (L.τ' b) (CpO η) (L.bvar b) η (L.etaW b η ηW) ∧
      LiftCini (L.cpy b) (CpO η) η (L.etaW b η ηW) := by
  -- a ♭ label with any non-blank ghost is not fresh
  have nf_sto : ∀ l c, η.sto l = some c → ¬ P.Tail b l := fun l c h hf => by rw [hs.sto l hf] at h; cases h
  have nf_box : ∀ l B, η.box l = some B → ¬ P.Tail b l := fun l B h hf => by rw [hs.box l hf] at h; cases h
  have nf_pfr : ∀ l q, η.pfr l = some q → ¬ P.Tail b l := fun l q h hf => by rw [hs.pfr l hf] at h; cases h
  have nf_seen : ∀ l, η.seen l → ¬ P.Tail b l := fun l h hf => hs.seen l hf h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hw
  · exact hp
  · exact ht
  · exact «τ'σ'» hM hb
  · exact «σ'τ'» hM hb
  · intro l c h
    show L.stoE b η ηW (L.σ' b l) = some c
    unfold stoE; rw [cls_img hM hb l _ _ _ _ (nf_sto l c h)]; exact h
  · intro l
    show η.ini l ≤ L.iniE b η ηW (L.σ' b l)
    by_cases hf : P.Tail b l
    · rw [hs.ini l hf]; exact Nat.zero_le _
    · unfold iniE; rw [cls_img hM hb l _ _ _ _ hf]; exact Nat.le_refl _
  · intro l
    show η.rini l ≤ L.riniE b η ηW (L.σ' b l)
    by_cases hf : P.Tail b l
    · rw [hs.rini l hf]; exact Nat.zero_le _
    · unfold riniE; rw [cls_img hM hb l _ _ _ _ hf]; exact Nat.le_refl _
  · intro l q h
    show L.pfrE b η ηW (L.σ' b l) = some q
    unfold pfrE; rw [cls_img hM hb l _ _ _ _ (nf_pfr l q h)]; exact h
  · intro l h
    show L.seenE b η ηW (L.σ' b l)
    unfold seenE; rw [cls_img hM hb l _ _ _ _ (nf_seen l h)]; exact h
  · intro l c h1 h2 h3; exact ⟨c, h1, h2, h3⟩
  · intro l c hc h
    refine ⟨{ c with owner := none }, ?_, rfl⟩
    show L.stoE b η ηW (L.cpy b l) = some { c with owner := none }
    unfold stoE; rw [cls_cpy hM hb]; simp only [hc, if_true, h, Option.map_some]
  · intro l _
    show η.rc l ≤ L.riniE b η ηW (L.cpy b l)
    unfold riniE; rw [cls_cpy hM hb]; exact Nat.le_refl _
  · intro l hl
    refine ⟨0, ?_, fun v => Nat.zero_le v⟩
    show L.pfrE b η ηW (L.cpy b l) = some 0
    unfold pfrE; rw [cls_cpy hM hb, if_pos hl]
  · intro l B h
    refine ⟨B.pay.map (rl (L.σ' b)), List.length_map _, ?_⟩
    show L.boxE b η ηW (L.σ' b l) = _
    unfold boxE; rw [cls_img hM hb l _ _ _ _ (nf_box l B h), h]; rfl
  · intro l B _ h
    refine ⟨B.pay.map (rl (L.σ' b)), List.length_map _, ?_⟩
    show L.boxE b η ηW (L.cpy b l) = _
    unfold boxE; rw [cls_cpy hM hb, h]; rfl
  · intro x B k h
    show L.boxE b η ηW (L.bvar b x k) = _
    unfold boxE; rw [cls_bvar hM hb, h]; rfl
  · intro x k q h
    show L.pfrE b η ηW (L.bvar b x k) = some q
    unfold pfrE; rw [cls_bvar hM hb]; exact h
  · intro x k h
    show L.seenE b η ηW (L.bvar b x k)
    unfold seenE; rw [cls_bvar hM hb]; exact h
  · intro x k
    show η.ini x ≤ L.iniE b η ηW (L.bvar b x k)
    unfold iniE; rw [cls_bvar hM hb]; exact Nat.le_refl _
  · intro x k
    show η.rini x ≤ L.riniE b η ηW (L.bvar b x k)
    unfold riniE; rw [cls_bvar hM hb]; exact Nat.le_refl _
  · intro l _
    show η.rc l ≤ L.iniE b η ηW (L.cpy b l)
    unfold iniE; rw [cls_cpy hM hb]; exact Nat.le_refl _

end Lv

/-- The relation between the caller's W env `ηW` and its ♭ partner `ηB` at level `L` (the F4 invariant):
off the old copy/variant labels, `ηW` is `ηB` moved by `σ` (boxes with payloads mapped by `σ`); `ηW` is blank on
the untouched columns; W payloads mention no old copy/variant. -/
structure RelW {P : Plan} (L : Lv P) (ηW ηB : TEnv) : Prop where
  coh : Coh ηW
  fsto : ∀ m, P.Fresh L.c₀ m → P.Tail L.bnd m → ηW.sto m = none
  fbox : ∀ m, P.Fresh L.c₀ m → P.Tail L.bnd m → ηW.box m = none
  fini : ∀ m, P.Fresh L.c₀ m → P.Tail L.bnd m → ηW.ini m = 0
  frini : ∀ m, P.Fresh L.c₀ m → P.Tail L.bnd m → ηW.rini m = 0
  fpfr : ∀ m, P.Fresh L.c₀ m → P.Tail L.bnd m → ηW.pfr m = none
  fseen : ∀ m, P.Fresh L.c₀ m → P.Tail L.bnd m → ¬ ηW.seen m
  sto : ∀ m c, ¬ L.Old m → ηW.sto m = some c → ηB.sto (L.τ m) = some c
  ini : ∀ m, ¬ L.Old m → ηW.ini m ≤ ηB.ini (L.τ m)
  rini : ∀ m, ¬ L.Old m → ηW.rini m ≤ ηB.rini (L.τ m)
  pfr : ∀ m q, ¬ L.Old m → ηW.pfr m = some q → ηB.pfr (L.τ m) = some q
  seen : ∀ m, ¬ L.Old m → ηW.seen m → ηB.seen (L.τ m)
  box : ∀ m B, ¬ L.Old m → ηW.box m = some B →
    ∃ B', ηB.box (L.τ m) = some B' ∧ B = { B' with pay := B'.pay.map (rl L.σ) }
  pay : ∀ x B, ηB.box x = some B → ∀ w ∈ B.pay, ∀ a g, w.val = .loc a g → ¬ L.Old (L.σ a.label)
  rid : ηW.rid ≤ ηB.rid
  wit : ηW.wit = ηB.wit
  prog : ηW.prog = ηB.prog
  tid : ηW.tid = ηB.tid
  -- the old copies/variants (`L.Old`) against their ♭ originals `L.og m`
  vsto : ∀ m, L.cpb m → ηW.sto m = none
  ocl : ∀ m c', L.Old m → ηW.sto m = some c' →
    ∃ c, ηB.sto (L.og m) = some c ∧ c'.ty = c.ty ∧ c'.owner = none ∧ c.owner = some ηB.tid
  oinil : ∀ m c', L.Old m → ηW.sto m = some c' → ηW.ini m ≤ ηB.rc (L.og m)
  orinil : ∀ m c', L.Old m → ηW.sto m = some c' → ηW.rini m ≤ ηB.rc (L.og m)
  opfrl : ∀ m c', L.Old m → ηW.sto m = some c' → ∃ q, ηB.pfr (L.og m) = some q
  opfrc : ∀ m c', L.Old m → ηW.sto m = some c' → ∃ q, ηW.pfr m = some q ∧ ∀ v : WeakMem.Ts, q ≤ v
  oini : ∀ m, L.Old m → ηW.sto m = none → ηW.ini m ≤ ηB.ini (L.og m)
  orini : ∀ m, L.Old m → ηW.sto m = none → ηW.rini m ≤ ηB.rini (L.og m)
  opfr : ∀ m q, L.Old m → ηW.sto m = none → ηW.pfr m = some q → ηB.pfr (L.og m) = some q
  oseen : ∀ m, L.Old m → ηW.sto m = none → ηW.seen m → ηB.seen (L.og m)
  obox : ∀ m B, L.Old m → ηW.box m = some B → ηB.box (L.og m) = some { B with pay := B.pay.map (rl L.og) }
  opay : ∀ m B, L.Old m → ηW.box m = some B → ∀ w ∈ B.pay, ∀ a g, w.val = .loc a g →
    L.Old a.label ∨ ¬ P.Fresh L.c₀ a.label ∨ ¬ P.Tail L.bnd a.label

namespace Lv
variable {P : Plan} {L : Lv P} {b : Nat}
variable (hM : L.c₀ + 3 ≤ P.M) (hb : P.N ≤ b)
include hM hb

theorem Old_not_Fresh {m : WeakMem.AllocLabel} (h : L.Old m) : ¬ P.Fresh L.c₀ m :=
  fun hf => Plan.not_Used_of_Fresh hf (Old_Used h)

theorem cls_old {α : Type} {m : WeakMem.AllocLabel} (ho : L.Old m) (fc : WeakMem.AllocLabel → α)
    (fv : Nat → Nat → α) (fw fb : WeakMem.AllocLabel → α) : L.cls b m fc fv (L.oth b fw fb) = fw m := by
  unfold cls
  have h0 : ¬ ∃ l, m = L.cpy b l := fun ⟨l, e⟩ => cpy_not_Old hM hb l (e ▸ ho)
  have h1 : ¬ ∃ p : Nat × Nat, m = L.bvar b p.1 p.2 := fun ⟨p, e⟩ => bvar_not_Old hM hb p.1 p.2 (e ▸ ho)
  rw [dif_neg h0, dif_neg h1]; unfold oth; rw [if_pos ho]

omit hM hb in
theorem Tail_mono {b₁ b₂ : Nat} (h : b₁ ≤ b₂) {m : WeakMem.AllocLabel} (ht : P.Tail b₂ m) : P.Tail b₁ m := by
  obtain ⟨k, hk, e⟩ := ht; exact ⟨k, Nat.le_trans h hk, e⟩

theorem cls_mid {α : Type} (hbb : L.bnd ≤ b) {m : WeakMem.AllocLabel} (ho : ¬ L.Old m)
    (hf : ¬ (P.Fresh L.c₀ m ∧ P.Tail L.bnd m))
    (fc : WeakMem.AllocLabel → α) (fv : Nat → Nat → α) (fw fb : WeakMem.AllocLabel → α) :
    L.cls b m fc fv (L.oth b fw fb) = fb (L.τ m) := by
  unfold cls
  have h0 : ¬ ∃ l, m = L.cpy b l := fun ⟨l, e⟩ =>
    hf ⟨e ▸ cpy_Fresh hM hb l, Tail_mono hbb (e ▸ tail_cpy hM hb l)⟩
  have h1 : ¬ ∃ p : Nat × Nat, m = L.bvar b p.1 p.2 := fun ⟨p, e⟩ =>
    hf ⟨e ▸ bvar_Fresh hM hb p.1 p.2, Tail_mono hbb (e ▸ tail_bvar hM hb p.1 p.2)⟩
  rw [dif_neg h0, dif_neg h1]; unfold oth; rw [if_neg ho]
  congr 1
  exact «τ'_eq_τ» hM hb ho (fun v _ e => hf ⟨e ▸ mv_Fresh hM hb v, Tail_mono hbb (e ▸ tail_mv hM hb v)⟩)

omit hM hb in
/-- `σ` maps the used columns into themselves. -/
theorem σ_Used {m : WeakMem.AllocLabel} (h : P.Used L.c₀ m) : P.Used L.c₀ (L.σ m) := by
  rcases Classical.em (P.Used L.c₀ (L.σ m)) with h' | hn
  · exact h'
  · have e := L.fix _ hn
    have : L.σ m = m := by have := congrArg L.τ e; rw [L.sl, L.sl] at this; rw [this]
    exact absurd (by rw [this]; exact h) hn

/-- On a payload label of `η` (off the tail, not mapped to an old object), `σ′` is `σ`. -/
theorem σ'_pay {a : WeakMem.AllocLabel} (ht : ¬ P.Tail b a) (ho : ¬ L.Old (L.σ a)) : L.σ' b a = L.σ a := by
  refine «σ'_eq_σ» hM hb ho (fun v _ e => ?_)
  by_cases hu : P.Used L.c₀ a
  · exact Plan.not_Used_of_Fresh (mv_Fresh hM hb v) (e ▸ σ_Used hu)
  · have : L.σ a = a := L.fix a hu
    rw [this] at e; exact ht (e ▸ tail_mv hM hb v)

omit hM hb in
theorem map_rl_congr {f g : WeakMem.AllocLabel → WeakMem.AllocLabel} :
    ∀ (ws : List Word), (∀ w ∈ ws, ∀ a k, w.val = .loc a k → f a.label = g a.label) → ws.map (rl f) = ws.map (rl g)
  | [], _ => rfl
  | w :: ws, h => by
    simp only [List.map_cons]
    congr 1
    · cases w with
      | mk v vw rt =>
        cases v with
        | loc a k =>
          have := h _ (List.mem_cons_self) a k rfl
          simp [rl, rlv, this]
        | _ => simp [rl, rlv]
    · exact map_rl_congr ws (fun w hw => h w (by simp [hw]))

/-- **ext_ok**: the level's `η″` extends the caller's W env. -/
theorem ext_ok (hbb : L.bnd ≤ b) {ηW ηB η : TEnv} (hr : RelW L ηW ηB) (he : ExtB ηB η) (hs : FreshSup P b η) :
    Ext ηW (L.etaW b η ηW) := by
  obtain ⟨-, -, -, -, hEs, hEi, hEp, hEse, hEb, hErid, -, hEri⟩ := he
  refine Ext_withSto hr.coh (fun m c h => ?_) (fun m => ?_) (fun m q h => ?_) (fun m h => ?_) (fun m B h => ?_)
    (Nat.le_trans hr.rid hErid) η.fp _ (fun m => ?_)
  · show L.stoE b η ηW m = some c
    unfold stoE
    by_cases ho : L.Old m
    · rw [cls_old hM hb ho]; exact h
    · have hf : ¬ (P.Fresh L.c₀ m ∧ P.Tail L.bnd m) := fun hf => by rw [hr.fsto m hf.1 hf.2] at h; cases h
      rw [cls_mid hM hb hbb ho hf]; exact hEs _ _ (hr.sto m c ho h)
  · show ηW.ini m ≤ L.iniE b η ηW m
    unfold iniE
    by_cases ho : L.Old m
    · rw [cls_old hM hb ho]; exact Nat.le_refl _
    · by_cases hf : P.Fresh L.c₀ m ∧ P.Tail L.bnd m
      · rw [hr.fini m hf.1 hf.2]; exact Nat.zero_le _
      · rw [cls_mid hM hb hbb ho hf]; exact Nat.le_trans (hr.ini m ho) (hEi _)
  · show L.pfrE b η ηW m = some q
    unfold pfrE
    by_cases ho : L.Old m
    · rw [cls_old hM hb ho]; exact h
    · have hf : ¬ (P.Fresh L.c₀ m ∧ P.Tail L.bnd m) := fun hf => by rw [hr.fpfr m hf.1 hf.2] at h; cases h
      rw [cls_mid hM hb hbb ho hf]; exact hEp _ _ (hr.pfr m q ho h)
  · show L.seenE b η ηW m
    unfold seenE
    by_cases ho : L.Old m
    · rw [cls_old hM hb ho]; exact h
    · have hf : ¬ (P.Fresh L.c₀ m ∧ P.Tail L.bnd m) := fun hf => hr.fseen m hf.1 hf.2 h
      rw [cls_mid hM hb hbb ho hf]; exact hEse _ (hr.seen m ho h)
  · show L.boxE b η ηW m = some B
    unfold boxE
    by_cases ho : L.Old m
    · rw [cls_old hM hb ho]; exact h
    · have hf : ¬ (P.Fresh L.c₀ m ∧ P.Tail L.bnd m) := fun hf => by rw [hr.fbox m hf.1 hf.2] at h; cases h
      rw [cls_mid hM hb hbb ho hf]
      obtain ⟨B', hB', rfl⟩ := hr.box m B ho h
      rw [hEb _ _ hB']
      simp only [Option.map_some]
      congr 2
      exact map_rl_congr B'.pay (fun w hw a k hv =>
        σ'_pay hM hb (hs.pay _ _ (hEb _ _ hB') w hw a k hv) (hr.pay _ _ hB' w hw a k hv))
  · show ηW.rini m ≤ L.riniE b η ηW m
    unfold riniE
    by_cases ho : L.Old m
    · rw [cls_old hM hb ho]; exact Nat.le_refl _
    · by_cases hf : P.Fresh L.c₀ m ∧ P.Tail L.bnd m
      · rw [hr.frini m hf.1 hf.2]; exact Nat.zero_le _
      · rw [cls_mid hM hb hbb ho hf]; exact Nat.le_trans (hr.rini m ho) (hEri _)

end Lv
end TermSound.Flat
