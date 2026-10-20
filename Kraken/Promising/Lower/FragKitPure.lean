/-
**The allocating Treiber client's `main` is
pure, as one placement-independent fragment specification; the kit's `pure`
field from it.** ISA: AArch64; machine: the executable
machine's per-thread environment semantics, partial correctness; env
`RP rel = counted (relPure Arch.armv8 rel)` (the kit's `LowerCore.pure` env).

The allocation pilot (`Lower/AllocPure.lean`) and the publish pilot (`Lower/PublishPure.lean`) proved
`main`'s purity twice, each at its own text (`main_pure`, block lemmas
mentioning the end address `mainEnd` and `<prog>_placed`). As the fragment kit did for
`main` (`Lower/FragKitMain.lean`), it is proved here once, with the runtime's
return address `ra` in place of `mainEnd`:

- `MainPreRF`: the original `MainPreR` with `ra` for `mainEnd` (so the original
  `MainPreR` is `MainPreRF` at the end of the text, definitionally).
- `tail_pure`: the tail (`ret_pop:` … `ret`) as a `FragSpecEnv` in `RP rel`.
- `main_save_pureF`, `main_init_pureF`, `main_mid_pureF`: the straight-line
  blocks, the allocation pilot's with `ra` for `mainEnd`; `main_body_pure`: the three calls
  through `FunSpecPartialEnv` hypotheses.
- **`main_pure_fragL`**: `main`'s purity as a `FragSpecEnvL` over
  `F :: allocFrag :: popFrag :: Gp`, generic in the push entry `lp` (with a
  relPure spec over `Gp`: `(Pilot.pushFrag_pure …).toL`,
  `Publish.pushp_pure`) and the fragment `F` holding `main`'s first block and
  the tail (both decidable), like `FragKit.main_fragL`. `alloc` by
  `Alloc.allocFrag_spec` at `rpFenceMono`, `pop` by `Pilot.popFrag_pure`.
- `Kit.LowerStatic`: `LowerCore`'s fields without the relPure twin
  (`PreR`/`QR`/`pure`); **`LowerStatic.ofFragPure`** fills `pure` from a
  relPure fragment spec of `main` by `Kit.partialTripleEnv_of_fragL` (env
  `counted (relPure A rel)`), side conditions as for `LowerThread.ofFrag`.

`Lower/FragKitPublish2.lean` re-derives `publish_promising` and
`alloc_promising` with both `main` and `pure` from the fragment route.
-/
import Kraken.Promising.Lower.KitFrag
import Kraken.Promising.Lower.FragKitMain

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Kit

/-- **A lowered thread's static part**: `LowerCore` without the relPure twin
(layout, text, plan, static facts, stuck-at-end, the counted post `Q` and its
`hB`; fields as in `LowerCore`). -/
structure LowerStatic (A : Arch) (tid : Nat) (B : Config isa → Res → Ghost → Prop) where
  l : _root_.Layout
  p : Program
  valid : Kraken.Executable.ValidLayout (l p)
  pl : Plan
  hpl : pl.Valid
  live : (l p).rmwLive = true
  shape : Phase1TreeF (l p)
  stuck : ∀ (env : SharedEnv) x R, x.1.2 = (l p).addrOf p.length → ¬ (l p).instrStepEnv env x R
  Q : MachineData → EStateA × Nat → Prop
  hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf (layout := l) p (fun s g => ∃ n, Q s (g, n)) (t.st.st, σ) →
    t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g

/-- **A `LowerCore` from the static part and a relPure fragment spec of
`main`** (in `counted (relPure A rel)`, over fragments held by `S.p`, which
starts with `main`'s label; `partialTripleEnv_of_fragL`). `PreR`/`QR` are the
kit's; `hpre`/`hpost` read the spec at the end of the text. -/
noncomputable def LowerStatic.ofFragPure {A : Arch} {tid : Nat} {B : Config isa → Res → Ghost → Prop}
    (rel : Loc → Pred) (S : LowerStatic A tid B) {p' : Program} {frags : List Program} {lm : Label}
    {FPre : Int64 → MachineData → (SharedEnv.counted (SharedEnv.relPure A rel)).State → Prop}
    {FPost : Int64 → MachineData → (SharedEnv.counted (SharedEnv.relPure A rel)).State → MachineData →
      (SharedEnv.counted (SharedEnv.relPure A rel)).State → Prop}
    (h : FragSpecEnvL (SharedEnv.counted (SharedEnv.relPure A rel)) frags lm FPre FPost)
    (hwf : Program.WF S.p) (hp : S.p = Directive.label lm :: p') (hne : S.p.any (fun d => !d.isLabel) = true)
    (hs : frags.all (fun q => Program.subBlocksOfE q S.p) = true)
    (PreR QR : MachineData → (SharedEnv.counted (SharedEnv.relPure A rel)).State → Prop)
    (hpre : ∀ s g, PreR s g → FPre ((S.l S.p).addrOf S.p.length) s g)
    (hpost : ∀ s g s' g', PreR s g → FPost ((S.l S.p).addrOf S.p.length) s g s' g' → QR s' g') :
    LowerCore A tid rel B :=
  { S with
    PreR := PreR
    QR := QR
    pure := @partialTripleEnv_of_fragL S.l S.p p' S.valid _ frags lm FPre FPost h hwf hp hne hs PreR QR hpre hpost }

end Kraken.Promising.Lower.Kit

namespace Kraken.Promising.Lower.FragKit

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP tailFrag mainMid popFrag popFrag_pure)
open Kraken.Promising.Lower.Alloc (mainInit mainSave rpFenceMono AllocPre AllocPost allocFrag allocFrag_spec)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- At `main`, relPure: `x30 = ra`, `x21 = t`, `x27 = n` with room, no `dmem`
word (the original `MainPreR` with `ra` for `mainEnd`). -/
def MainPreRF (rel : Loc → Pred) (t n : BitVec 64) (ra : Int64) (s : MachineData) (_ : (RP rel).State) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = ra ∧ s.regs.X21.toBitVec = t ∧ s.regs.X27.toBitVec = n ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s

/-! ## The tail -/

/-- **The tail is pure, placement-independent**: from `ret_pop` it returns to
the link saved in `x19` (the allocation pilot's `main_tail_pure`, `ra` for `mainEnd`). -/
theorem tail_pure (rel : Loc → Pred) :
    FragSpecEnv (RP rel) tailFrag "ret_pop" (fun ra s _ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ NoDmem s)
      (fun _ _ _ _ _ => True) := by
  refine FragSpecEnv.of_cfg (fun ra _ _ lb s _ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧
      (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
      (lb = "ret_pop" ∨ lb = "empty")) rfl (by decide)
    (fun ra t g ⟨h19, ⟨hd8, hd4⟩⟩ => ⟨h19, hd8, hd4, .inl rfl⟩) ?_
  intro _ ra t g _
  cfg_cases_env [tailFrag]
  all_goals (intro s₀ g₀; vcgen)
  all_goals obtain ⟨⟨h19, hd8, hd4, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [h19, hd8, hd4, SharedEnv.relPureQ]; done)
  exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using h19, by simpa using hd8, by simpa using hd4,
    .inr rfl⟩, .inl (by decide)⟩)

/-! ## The straight-line blocks (the allocation pilot's, `ra` for `mainEnd`) -/

variable [CodeEnv]

theorem main_save_pureF (rel : Loc → Pred) (t n : BitVec 64) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => MainPreRF rel t n ra s σ ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mainSave⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X21.toBitVec = t ∧
        s.regs.X27.toBitVec = n ∧ s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainSave
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp [NoDmem, h30, h21, h27, hd8, hd4]
  exact h27 ▸ hlim

/-- The initial stores are pure (`[n]`, `[n + 8]`). -/
theorem main_init_pureF (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (s.regs.X0.toBitVec = n ∧
        Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X21.toBitVec = t ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainInit⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ Int64.ofBitVec s.regs.X19.toBitVec = ra ∧
        s.regs.X21.toBitVec = t ∧ NoDmem s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainInit
  vcgen
  all_goals obtain ⟨⟨h0, h19, h21, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem] at *
  case vc2 => rw [h0]; exact hd _
  case vc4 => rw [h0]; exact hn _
  case vc5 =>
    rename_i hst1 hst2 _
    simp [hd4] at hst1
    obtain ⟨rfl, -⟩ := hst1
    simp [hd8] at hst2
    obtain ⟨rfl, -⟩ := hst2
    exact ⟨h21, h0, h19, h21, hd8, hd4⟩

theorem main_mid_pureF (rel : Loc → Pred) (t : BitVec 64) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X19.toBitVec = ra ∧
        s.regs.X21.toBitVec = t ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mainMid⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = t ∧ Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainMid
  vcgen
  all_goals obtain ⟨⟨h19, h21, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp [NoDmem, h19, h21, hd8, hd4]

/-! ## The body: three calls -/

section
attribute [local simp] MachineData.lr MachineData.setLr Reg64s.setXReg

/-- **`main`'s first block is pure**: three calls through their relPure
specifications, at any code where those hold (`lp` the push entry). -/
theorem main_body_pure (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) {lp : Label}
    (hA : FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "alloc")
      (AllocPre (RP rel) (fun _ => True) n) (AllocPost (RP rel) (fun _ => True) n))
    (hPu : FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label lp)
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s'))
    (hPo : FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s'))
    (ra : Int64) (s : MachineData) (σ : (RP rel).State) (hpre : MainPreRF rel t n ra s σ) :
    PartialWpEnv (RP rel) (mainBodyG lp) (fun s _ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ NoDmem s)
      (fun _ _ _ => False) s σ := by
  have h1 := (main_save_pureF rel t n ra s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
  rintro s1 σ1 ⟨h19, h21, h27, hlim, ⟨hd8, hd4⟩⟩
  refine PartialWpEnv.call hA fun ra' => ⟨⟨by simp, by simpa using h27, by simpa using hlim, trivial⟩, ?_⟩
  rintro s2 σ2 ⟨a0, -, ⟨f19, -, f21, -, -, -, -, -, -, fdm⟩, -⟩
  have h2 := (main_init_pureF rel t n hd hn ra s2 σ2).le_wp s2 σ2 ⟨⟨a0, by simpa [f19] using h19,
    by simpa [f21] using h21, ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
  clear h19 h21 hd8 hd4
  rintro s3 σ3 ⟨h0, h1, h19, h21, ⟨hd8, hd4⟩⟩
  refine PartialWpEnv.call hPu fun ra' =>
    ⟨⟨by simp, by simpa using h0, by simpa using h1, ⟨by simpa using hd8, by simpa using hd4⟩⟩, ?_⟩
  rintro s4 σ4 ⟨f19, -, f21, -, -, -, -, -, -, -, fdm⟩
  have h3 := (main_mid_pureF rel t ra s4 σ4).le_wp s4 σ4 ⟨⟨by simpa [f19] using h19, by simpa [f21] using h21,
    ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h3
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h3)
  rintro s5 σ5 ⟨h0', h19', ⟨hd8', hd4'⟩⟩
  refine PartialWpEnv.call hPo fun ra' =>
    ⟨⟨by simp, by simpa using h0', ⟨by simpa using hd8', by simpa using hd4'⟩⟩, ?_⟩
  rintro s6 σ6 ⟨g19, -, -, -, -, -, -, -, -, -, gdm⟩
  exact PartialWpEnv.nil ⟨by simpa [g19] using h19', ⟨by simpa [gdm] using hd8', by simpa [gdm] using hd4'⟩⟩

end

omit [CodeEnv]

/-! ## `main`'s purity, once -/

/-- **`main` is pure, placement-independent and generic in the push entry**:
for every push entry `lp` with a relPure spec over `Gp` and every fragment
`F` holding `main`'s first block (falling into `ret_pop`) and the tail, `main`
from `MainPreRF` returns to `ra`, in every code placing `F`, `alloc`, `pop`
and `Gp` (the relPure twin of `main_fragL`). -/
theorem main_pure_fragL (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) {F : Program} {lp : Label} {Gp : List Program}
    (hpush : FragSpecEnvL (RP rel) Gp lp
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s'))
    (hb : Program.blockAt F "main" = some ⟨"main", mainBodyG lp, some "ret_pop"⟩)
    (ht : Program.subBlocksOfE tailFrag F = true) :
    FragSpecEnvL (RP rel) (F :: allocFrag :: popFrag :: Gp) "main" (MainPreRF rel t n)
      (fun _ _ _ _ _ => True) := by
  refine ⟨fun hpl ra s g hp => ?_⟩
  have hF := hpl F List.mem_cons_self
  have hA := (@allocFrag_spec (RP rel) (rpFenceMono rel) (fun _ => True) (fun _ _ _ _ => trivial) n).spec
    (hpl _ (by simp))
  have hPu := hpush.at_sub hpl fun q hq => by simp [hq]
  have hPo := (popFrag_pure rel t).spec (hpl _ (by simp))
  refine Safely.bind (main_body_pure rel t n hd hn hA hPu hPo ra s g hp _ (hF.block _ _ hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, h19, hdm⟩ | hF')
  · dsimp only at ha h19 hdm
    rw [hF.next _ _ _ hb rfl] at ha
    subst ha
    exact ((tail_pure rel).spec (hF.of_sub ht) ra s' g' ⟨h19, hdm⟩).mono fun _ ⟨hx, _⟩ => ⟨hx, trivial⟩
  · exact hF'.elim

end Kraken.Promising.Lower.FragKit
