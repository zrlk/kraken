/-
**Part 2: `arenaP` is pure** in `RP rel` for release
predicates pure at both nodes' words: `[n]`, `[n + 16]` (4 bytes) and
`[n + 8]`, `[n + 16 + 8]` (8 bytes). ISA: AArch64;
machine: the executable machine's per-thread environment semantics
(`relPure` environment), partial correctness.

- `alloc`, `push`, `pop` by the existing **fragment specifications**
  (`Alloc.allocFrag_spec`, `Pilot.pushFrag_pure`, `Pilot.popFrag_pure`),
  transported to `arenaP` in one line each (`FragSpecEnv.of_placed`).
- **Alloc chaining** (`alloc_chain`): `alloc_spec`'s post at `n` with room for a
  second node is its pre at `n + 16`; the two calls return `n` and `n + 16`.
- `main_init1_pure`, `main_init2_pure` (the initial stores), `main_save_pure`,
  `main_mid_pure`, `main_tail_pure` at `arenaP`, and `main_pure`.

The per-`k` cost of this file is one `alloc` call, one init block and one
`push` call per allocation in `main_body`, and one purity hypothesis per node
word.
-/
import Kraken.Promising.Lower.ArenaProg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Arena

open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP tailFrag mainMid pushFrag_pure popFrag_pure)
open Kraken.Promising.Lower.Alloc (AllocPre AllocPost AllocSaved allocFrag_spec rpFenceMono mainSave mainInit)
open Kraken.AArch64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The initial stores of `new {v2, null}` (payload `w22`) and `push`'s arguments. -/
def mainInit2 : Program := parseAArch64("
    str w22, [x0]
    str xzr, [x0, #8]
    mov x1, x0
    mov x0, x21
")

/-- `main`'s first block, up to `ret_pop`: two allocations and pushes, one pop. -/
def mainBody : Program :=
  mainSave ++ (Directive.instr ⟨.W64, .BL (.label "alloc")⟩ :: (mainInit ++
    (Directive.instr ⟨.W64, .BL (.label "push")⟩ :: (Directive.instr ⟨.W64, .BL (.label "alloc")⟩ :: (mainInit2 ++
    (Directive.instr ⟨.W64, .BL (.label "push")⟩ :: (mainMid ++ [Directive.instr ⟨.W64, .BL (.label "pop")⟩])))))))

theorem arenaP_main_block : Program.blockAt arenaP "main" = some ⟨"main", mainBody, some "ret_pop"⟩ := by
  decide +kernel

/-! ## Alloc chaining -/

/-- **Alloc chaining**: after `alloc` at `n` (`AllocPost`), with room for a
second node below the unchanged limit, `alloc`'s pre holds at `n + 16` for any
link `ra'`; with `alloc_spec` the `i`-th call returns `n + 16 · i`. -/
theorem alloc_chain {env : SharedEnv} {R : env.State → Prop} {n : BitVec 64} {ra : Int64} {t t' : MachineData}
    {g g' : env.State} (h : AllocPost env R n ra t g t' g') (hroom : n + 16 + 16 ≤ t.regs.X28.toBitVec)
    (ra' : Int64) : AllocPre env R (n + 16) ra' (t'.setLr ra') g' := by
  obtain ⟨-, h27, ⟨-, -, -, -, -, -, -, -, h28, -⟩, hR⟩ := h
  refine ⟨by simp [MachineData.lr, MachineData.setLr], ?_, ?_, hR⟩
  · simpa [MachineData.setLr, Reg64s.setXReg] using h27
  · simpa [MachineData.setLr, Reg64s.setXReg, h27, h28] using hroom

variable [layout : _root_.Layout] [Executable.ValidLayout (layout arenaP)]

local instance arenaP.env : CodeEnv := ⟨layout arenaP⟩

omit layout [Executable.ValidLayout (layout arenaP)] in
theorem arenaP_wf : Program.WF arenaP := by decide +kernel

theorem arenaP_placed : Program.Placed arenaP "main" :=
  Program.placed_of_layout arenaP_wf rfl (by decide)

/-- The end of the text (the runtime's return address). -/
abbrev mainEnd : Int64 := (layout arenaP).addrOf arenaP.length

/-! ## The functions, from their fragment specifications -/

theorem alloc_pure (rel : Loc → Pred) (n : BitVec 64) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "alloc")
      (AllocPre (RP rel) (fun _ => True) n) (AllocPost (RP rel) (fun _ => True) n) :=
  (@allocFrag_spec (RP rel) (rpFenceMono rel) (fun _ => True) (fun _ _ _ _ => trivial) n).of_placed
    arenaP_placed (by decide)

theorem push_pure (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "push")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') :=
  (pushFrag_pure rel t n hn).of_placed arenaP_placed (by decide)

theorem pop_pure (rel : Loc → Pred) (t : BitVec 64) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (popFrag_pure rel t).of_placed arenaP_placed (by decide)

/-! ## `main`'s blocks -/

/-- The tail's purity table. -/
abbrev tailPTable (rel : Loc → Pred) : Label → MachineData → (RP rel).State → Prop :=
  fun lb s _ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ (lb = "ret_pop" ∨ lb = "empty")

theorem main_tail_pure (rel : Loc → Pred) : ∀ s (σ : (RP rel).State),
    Int64.ofBitVec s.regs.X19.toBitVec = mainEnd → NoDmem s →
    Safely (cenv.instrStepEnv (RP rel)) (fun x => x.1.2 = mainEnd)
      ((s, (_root_.Executable.labels cenv).label "ret_pop"), σ) := by
  rintro s σ h19 ⟨hd8, hd4⟩
  refine cfgEnv_partial_fun (p := tailFrag) (tailPTable rel) (E := fun a _ _ => a = mainEnd) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE arenaP_placed (by decide)) s σ ⟨h19, hd8, hd4, .inl rfl⟩
  cfg_cases_env [tailFrag]
  all_goals (intro s₀ g₀; vcgen)
  all_goals obtain ⟨⟨h19, hd8, hd4, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [h19, hd8, hd4, SharedEnv.relPureQ]; done)
  exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using h19, by simpa using hd8, by simpa using hd4,
    .inr rfl⟩, .inl (by decide)⟩)

omit [Executable.ValidLayout (layout arenaP)] in
theorem main_save_pure (rel : Loc → Pred) (t n : BitVec 64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X30.toBitVec = mainEnd ∧
        s.regs.X21.toBitVec = t ∧ s.regs.X27.toBitVec = n ∧ s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧
        NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mainSave⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = t ∧
        s.regs.X27.toBitVec = n ∧ s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ s.regs.X28 = s₀.regs.X28 ∧
        NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainSave
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp [NoDmem, h30, h21, h27, hd8, hd4]
  exact h27 ▸ hlim

omit [Executable.ValidLayout (layout arenaP)] in
theorem main_mid_pure (rel : Loc → Pred) (t : BitVec 64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧
        s.regs.X21.toBitVec = t ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mainMid⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = t ∧ Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainMid
  vcgen
  all_goals obtain ⟨⟨h19, h21, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp [NoDmem, h19, h21, hd8, hd4]

/-- The initial stores' frame: `push`'s arguments; `x19`, `x21`, `x27`, `x28`
unchanged; no `dmem` word. -/
def InitPost (n : BitVec 64) (s₀ s : MachineData) : Prop :=
  s.regs.X0.toBitVec = s₀.regs.X21.toBitVec ∧ s.regs.X1.toBitVec = n ∧ s.regs.X19 = s₀.regs.X19 ∧
    s.regs.X21 = s₀.regs.X21 ∧ s.regs.X27 = s₀.regs.X27 ∧ s.regs.X28 = s₀.regs.X28 ∧ NoDmem s

omit [Executable.ValidLayout (layout arenaP)] in
/-- Node 1's initial stores are pure (`[n]`, `[n + 8]`). -/
theorem main_init1_pure (rel : Loc → Pred) (n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (s.regs.X0.toBitVec = n ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainInit⟩ : EnvProgram (RP rel)) ⦃ (fun _ s _ => InitPost n s₀ s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainInit
  vcgen
  all_goals obtain ⟨⟨h0, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem, InitPost] at *
  case vc2 => rw [h0]; exact hd _
  case vc4 => rw [h0]; exact hn _
  case vc5 =>
    rename_i hst1 hst2 _
    simp [hd4] at hst1
    obtain ⟨rfl, -⟩ := hst1
    simp [hd8] at hst2
    obtain ⟨rfl, -⟩ := hst2
    exact ⟨h0, hd8, hd4⟩

omit [Executable.ValidLayout (layout arenaP)] in
/-- Node 2's initial stores are pure (`[n]`, `[n + 8]`). -/
theorem main_init2_pure (rel : Loc → Pred) (n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (s.regs.X0.toBitVec = n ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainInit2⟩ : EnvProgram (RP rel)) ⦃ (fun _ s _ => InitPost n s₀ s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainInit2
  vcgen
  all_goals obtain ⟨⟨h0, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem, InitPost] at *
  case vc2 => rw [h0]; exact hd _
  case vc4 => rw [h0]; exact hn _
  case vc5 =>
    rename_i hst1 hst2 _
    simp [hd4] at hst1
    obtain ⟨rfl, -⟩ := hst1
    simp [hd8] at hst2
    obtain ⟨rfl, -⟩ := hst2
    exact ⟨h0, hd8, hd4⟩

/-! ## `main` -/

/-- `main`'s pre: the return address, `&top`, the bump pointer `x27 = n` with
room for **two** nodes below `x28`, no `dmem` word. -/
def MainPreR (t n : BitVec 64) (s : MachineData) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = t ∧ s.regs.X27.toBitVec = n ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ n + 16 + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s

attribute [local simp] MachineData.lr MachineData.setLr Reg64s.setXReg in
/-- **`main`'s first block is pure**: five calls through their specifications,
the second `alloc` at `n + 16` (`alloc_chain`). -/
theorem main_body_pure (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n + 16, 4⟩) v)
    (hn2 : ∀ v : Val, Pred.Pure (rel ⟨n + 16 + 8, 8⟩) v) (s : MachineData) (σ : (RP rel).State)
    (hpre : MainPreR t n s) :
    PartialWpEnv (RP rel) mainBody
      (fun s _ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ NoDmem s) (fun _ _ _ => False) s σ := by
  obtain ⟨h30, h21, h27, hlim, hroom, hdm⟩ := hpre
  have h1 := (main_save_pure rel t n s σ).le_wp s σ ⟨⟨h30, h21, h27, hlim, hdm⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
  rintro s1 σ1 ⟨h19, h21, h27, hlim, h28, ⟨hd8, hd4⟩⟩
  refine PartialWpEnv.call (alloc_pure rel n) fun ra => ⟨⟨by simp, by simpa using h27, by simpa using hlim, trivial⟩, ?_⟩
  rintro s2 σ2 hA
  have hA2 := alloc_chain hA (by simpa [h28] using hroom)
  obtain ⟨a0, -, ⟨f19, -, f21, -, -, -, -, -, f28, fdm⟩, -⟩ := hA
  have h2 := (main_init1_pure rel n hd hn s2 σ2).le_wp s2 σ2
    ⟨⟨a0, ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
  rintro s3 σ3 ⟨i0, i1, i19, i21, i27, i28, ⟨id8, id4⟩⟩
  refine PartialWpEnv.call (push_pure rel t n hn) fun ra =>
    ⟨⟨by simp, by simpa [i21, f21, h21] using i0, by simpa using i1, ⟨by simpa using id8, by simpa using id4⟩⟩, ?_⟩
  rintro s4 σ4 ⟨g19, -, g21, -, -, -, -, -, g27, g28, gdm⟩
  have hA2' := hA2 0
  refine PartialWpEnv.call (alloc_pure rel (n + 16)) fun ra =>
    ⟨⟨by simp, ?_, ?_, trivial⟩, ?_⟩
  · simpa [g27, i27] using hA2'.2.1
  · simpa [g27, g28, i27, i28] using hA2'.2.2.1
  rintro s5 σ5 ⟨b0, -, ⟨k19, -, k21, -, -, -, -, -, k28, kdm⟩, -⟩
  have h3 := (main_init2_pure rel (n + 16) hd2 hn2 s5 σ5).le_wp s5 σ5
    ⟨⟨b0, ⟨by simpa [kdm, gdm] using id8, by simpa [kdm, gdm] using id4⟩⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h3
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h3)
  rintro s6 σ6 ⟨j0, j1, j19, j21, -, -, ⟨jd8, jd4⟩⟩
  refine PartialWpEnv.call (push_pure rel t (n + 16) hn2) fun ra =>
    ⟨⟨by simp, by simpa [j21, k21, g21, i21, f21, h21] using j0, by simpa using j1,
      ⟨by simpa using jd8, by simpa using jd4⟩⟩, ?_⟩
  rintro s7 σ7 ⟨l19, -, l21, -, -, -, -, -, -, -, ldm⟩
  have h4 := (main_mid_pure rel t s7 σ7).le_wp s7 σ7
    ⟨⟨by simpa [l19, j19, k19, g19, i19, f19] using h19, by simpa [l21, j21, k21, g21, i21, f21] using h21,
      ⟨by simpa [ldm] using jd8, by simpa [ldm] using jd4⟩⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h4
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h4)
  rintro s8 σ8 ⟨m0, m19, ⟨md8, md4⟩⟩
  refine PartialWpEnv.call (pop_pure rel t) fun ra =>
    ⟨⟨by simp, by simpa using m0, ⟨by simpa using md8, by simpa using md4⟩⟩, ?_⟩
  rintro s9 σ9 ⟨p19, -, -, -, -, -, -, -, -, -, pdm⟩
  exact PartialWpEnv.nil ⟨by simpa [p19] using m19, ⟨by simpa [pdm] using md8, by simpa [pdm] using md4⟩⟩

/-- **`main` is pure** (whole text), for release predicates pure at both
nodes' words. -/
theorem main_pure (rel : Loc → Pred) (t n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n + 16, 4⟩) v)
    (hn2 : ∀ v : Val, Pred.Pure (rel ⟨n + 16 + 8, 8⟩) v) :
    PartialTripleEnv (RP rel) (fun s _ => MainPreR t n s) arenaP (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  rw [← arenaP_placed.entry pc hpc]
  refine Safely.bind (main_body_pure rel t n hd hn hd2 hn2 s σ hpre _ (arenaP_placed.block _ _ arenaP_main_block)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, h19, hdm⟩ | hF)
  · dsimp only at ha h19 hdm
    rw [arenaP_placed.next _ _ _ arenaP_main_block rfl] at ha
    subst ha
    refine (main_tail_pure rel s' g' h19 hdm).mono fun x hx => .inl ⟨?_, trivial⟩
    obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := arenaP) arenaP [] 0 (by simp)
    rw [hx, arenaP_placed.entry _ hs0, Nat.zero_add] at *
    exact haf.symm
  · exact hF.elim

end Kraken.Promising.Lower.Arena
