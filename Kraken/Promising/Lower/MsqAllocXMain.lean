/-
**Part 2: `alloc`, the data-word store and
`main_e`** (counted `EEX P`, the x64 MS queue pilot's enqueuer environment) **and its purity
twin** (counted `EnvRT sAll`). ISA: x64; machine: the
executable machine's per-thread environment semantics, partial correctness
(`Safely`).

- `Safely.blockAtEnv` (generic): the x64 register-link pilot's `Safely.blockAt` for a block
  *with* shared accesses (an `EnvProgram` triple of its body).
- `allocFragX_spec`, **for every `FenceMonoX` environment** (`alloc` makes no
  memory access): from `r14 = n` with room below `r15`, returns `rax = n`,
  `r14 = n + 16`, the frame `AllocSavedX` (the x64 pilot's `Saved` except `r14`), any
  fence-stable `R` kept. The `ja alloc_oom` is refuted by the room (the table
  is empty at `alloc_oom`, so its zero-step self loop needs no rank).
- `vc_e_strD`: the x64 MS queue pilot's `E0` is kept by an 8-byte store to a non-queue word
  (the data word `[n + 8]`): pure there (`ghost₀` is `emp`), a positive share
  (`ComE`), not a planned release (`planE_rel`).
- `mainA_specX`: `main_e` by `Safely.blockAt`/`blockAtEnv` on its five blocks
  and the x64 register-link pilot's `jcall` at `alloc` (`allocFragX_spec`) and the x64 MS queue pilot's `enq`
  (`enq_fragXR`), all placed in `msqAX` (`FragSpecEnv.of_placed`). The second
  `alloc` returns `n1 + 16` (the bump pointer survives `enq`'s `Saved`), so
  the protocol's `n2` is `n1 + 16`.
- The twin (`mainA_pureX`): the same composition in counted `EnvRT sAll`,
  with `enq`'s twin `enq_pureX` (a `FragSpecEnv` of the x64 MS queue pilot's `enqFrag`: the frame
  kept, `dmem` empty) and the room carried across `enq` by `Saved`.
-/
import Kraken.Promising.Lower.MsqAllocXProg
import Kraken.Promising.Lower.MsqXRWhole

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

/-! ## A block with shared accesses at its label (generic) -/

section BlockEnv

variable [CodeEnv] {env : SharedEnv}

/-- **A block at its label, by an environment triple**: the block `blk` of the
placed text `p` at `l`, run from the exact `(s, g)` by an `EnvProgram` triple
of its body that never falls through, its exits `X` continuing. -/
theorem Safely.blockAtEnv {p : Program} {l : Label} {blk : Program.Block} (hpl : Program.PlacedIn p)
    (hb : Program.blockAt p l = some blk) {s : MachineData} {g : env.State}
    {X : Int64 → MachineData → env.State → Prop} {Q : MachineState × env.State → Prop}
    (h : ⦃ fun s' g' => s' = s ∧ g' = g ⦄ (⟨blk.body⟩ : EnvProgram env) ⦃ fun _ _ _ => False; X ⦄)
    (hk : ∀ a s' g', X a s' g' → Safely (cenv.instrStepEnv env) Q ((s', a), g')) :
    Safely (cenv.instrStepEnv env) Q ((s, (_root_.Executable.labels cenv).label l), g) := by
  have hw := h.le_wp s g ⟨rfl, rfl⟩
  rw [wpEnv_eq] at hw
  refine Safely.of_eventually_safely (hw _ (hpl.block l blk hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨-, hF⟩ | hx)
  · exact hF.elim
  · exact hk a s' g' hx

end BlockEnv

namespace Kraken.Promising.Lower.MsqAllocX

open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll mem_sAll8 EnvRT)
open Kraken.Promising.Lower.PilotX (Saved Saved.refl)
open Kraken.Promising.Lower.PilotXR (D8 ofBitVec_reg)
open Kraken.Promising.Lower.MsqXR (EnqPre EnqPost enq_fragXR enqFrag)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## `alloc` -/

/-- **The allocator's frame**: the x64 pilot's `Saved` except `r14`. -/
def AllocSavedX (t s : MachineData) : Prop :=
  s.regs.get64 .rbx = t.regs.get64 .rbx ∧ s.regs.get64 .rbp = t.regs.get64 .rbp ∧
    s.regs.get64 .r12 = t.regs.get64 .r12 ∧ s.regs.get64 .r13 = t.regs.get64 .r13 ∧
    s.regs.get64 .r15 = t.regs.get64 .r15 ∧ s.dmem = t.dmem

/-- `alloc`'s precondition: the link `r11 = ra`, `r14 = n` with room below
`r15`, `R`. -/
def AllocPreX (env : SharedEnv) (R : env.State → Prop) (n : BitVec 64) (ra : Int64) (t : MachineData)
    (g : env.State) : Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ t.regs.get64 .r14 = n ∧ t.regs.get64 .r14 + 16 ≤ t.regs.get64 .r15 ∧ R g

/-- `alloc`'s postcondition: `rax = n`, `r14 = n + 16`, the frame, `R`. -/
def AllocPostX (env : SharedEnv) (R : env.State → Prop) (n : BitVec 64) (_ : Int64) (t : MachineData)
    (_ : env.State) (t' : MachineData) (g' : env.State) : Prop :=
  t'.regs.get64 .rax = n ∧ t'.regs.get64 .r14 = n + 16 ∧ AllocSavedX t t' ∧ R g'

/-- `alloc`'s table: only its entry (the table is empty at `alloc_oom`). -/
abbrev allocTable (env : SharedEnv) (R : env.State → Prop) (n : BitVec 64) (ra : Int64) (t : MachineData)
    (_ : env.State) : Label → MachineData → env.State → Prop :=
  fun lb s g => lb = "alloc" ∧ s = t ∧ AllocPreX env R n ra t g

set_option hygiene false in
/-- `alloc`'s VCs: the `ja alloc_oom` refuted by the room, the return with
`rax = n`, `r14 = n + 16`, the frame and `R` (kept across the silent cells by
`hR`, if any). -/
local macro "alloc_vcs" : tactic => `(tactic| (
  intro _
  rintro ra t g -
  cfg_cases_env [allocFragX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hl, rfl, h11, h14, h15, hR0⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals try (exact absurd hl (by decide))
  all_goals have e16 : BitVec.setWidth 64 (Int64.toBitVec 16) = 16 := by decide
  case vc1 =>
    exfalso
    have hz := ‹CondCode.a.interp _ = true›
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hz
    rw [e16, BitVec.add_comm, MachineWP.ja_not_taken h15] at hz
    exact Bool.false_ne_true hz
  case vc2 =>
    refine .inr ⟨ofBitVec_reg h11, ?_⟩
    simp only [AllocPostX, AllocSavedX, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e16, h14, true_and]
    refine ⟨BitVec.add_comm _ _, ?_⟩
    repeat (first | exact hR0 | refine hR _ _ ?_ (by assumption))))

/-- **`alloc`'s specification**, in every `FenceMonoX` environment (the
fragment, every placement). -/
theorem allocFragX_spec (env : SharedEnv) [env.FenceMonoX] (R : env.State → Prop)
    (hR : ∀ g g', R g → SharedEnv.FenceMonoX.le g g' → R g') (n : BitVec 64) :
    FragSpecEnv env allocFragX "alloc" (AllocPreX env R n) (AllocPostX env R n) := by
  refine FragSpecEnv.of_cfg (allocTable env R n) rfl (by decide) (fun ra t g h => ⟨rfl, rfl, h⟩) ?_
  alloc_vcs

/-- **`alloc`'s specification in every `Skips` environment** (the
all-release twin's: silent cells leave the state unchanged). -/
theorem allocFragX_spec_skips (env : SharedEnv) [env.Skips] (R : env.State → Prop) (n : BitVec 64) :
    FragSpecEnv env allocFragX "alloc" (AllocPreX env R n) (AllocPostX env R n) := by
  refine FragSpecEnv.of_cfg (allocTable env R n) rfl (by decide) (fun ra t g h => ⟨rfl, rfl, h⟩) ?_
  alloc_vcs

/-! ## The data word's store -/

/-- **VC `movq %rcx, 8(%rax)`** (a store of any `v` to an 8-byte word `a`
that is not a queue word; here node `n`'s data word `[n + 8]`): permitted
(pure: `ghost₀` is `emp` off the queue words; a positive share from `ComE`;
not a planned release), and `E0` after it (the write set only gains a
message: no share changes; the own link message survives the snapshot's
growth). -/
theorem vc_e_strD {P : Params} {n a : BitVec 64} (ha : ¬ P.IsW ⟨a, 8⟩) (σ : EStateX) (h : E0 P n σ) (v : Val) :
    (EE P).ok (.store .plain false a 8 v) σ ∧
      ∀ b (σ' : EStateX), (EE P).step (.store .plain false a 8 v) σ b σ' → E0 P n σ' := by
  obtain ⟨⟨hW, hpos, htok⟩, hph⟩ := h
  refine ⟨⟨rfl, hpos a, fun _ => by rw [hW.rel_ne ha]; exact Pred.emp_pure _,
    fun hr => by rw [planE_rel] at hr; simp [ha] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, hws, -, -, -, ⟨_, -, hr⟩, -⟩ := step_storeFacts (pl := planE P) hs
  have hr' : σ'.r = σ.r.addW ⟨a, 8⟩ (v, tw) := by rw [hr]; unfold Plan.after; rw [planE_rel]; simp [ha]
  have hp := (TreiberCommon.AnchorOk.prefix hanc).trans (TreiberCommon.WriteSnap.prefix hws)
  refine ⟨⟨hW.mono hanc.ghost, fun a' => by rw [hr', Res.addW_q]; exact hpos a', ?_⟩, ?_⟩
  · unfold TokFrozen at *; rw [hr', Res.addW_q]; exact htok
  · unfold PhE TokFrozen at *
    simp only [hr', Res.addW_q]
    exact hph.imp id fun h => ⟨h.1, h.2.1, h.2.2.mono hp⟩

/-- A shared 8-byte store with `dmem` empty (any environment; the x64 register-link pilot's
`stS`, generalised). -/
theorem stG {E : SharedEnv} {d m : Std.ExtHashMap (BitVec 64) UInt8} {a r : BitVec 64}
    {g g' : (SharedEnv.counted E).State} (hd8 : ∀ a, Mem.loadInt d a 8 = none)
    (h : ((Mem.loadInt d a 8).isSome = true ∧ m = Mem.storeInt d a 8 r.toInt ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ m = d ∧ ∃ ok, E.step (.store .plain false a 8 (r.setWidth 128)) g.1 ok g'.1 ∧
        g'.2 = g.2 + (SharedAccess.store .plain false a 8 (r.setWidth 128)).tick)) :
    m = d ∧ (∃ ok, E.step (.store .plain false a 8 (r.setWidth 128)) g.1 ok g'.1) ∧ g.2 < g'.2 := by
  rcases h with ⟨hs, -, -⟩ | ⟨-, hm, ok, hs, ht⟩
  · rw [hd8] at hs; cases hs
  · exact ⟨hm, ⟨ok, hs⟩, by rw [ht]; simp [SharedAccess.tick]⟩

/-- `E0` across a silent cell of the counted environment. -/
theorem E0.fenceC {P : Params} {n : BitVec 64} {g g' : (SharedEnv.counted (EEX P)).State} (h : E0 P n g.1)
    (hf : X64.EnvG.FenceLe g.1 g'.1 ∧ g'.2 = g.2) : E0 P n g'.1 :=
  h.fence hf.1

/-! ## `main_e` -/

theorem blockAt_mainA : Program.blockAt msqAX "main_e" = some ⟨"main_e", mainABody, some "ret_a1"⟩ := by decide
theorem blockAt_retA1 : Program.blockAt msqAX "ret_a1" = some ⟨"ret_a1", retA1Body, some "ret_e1"⟩ := by decide
theorem blockAt_retE1 : Program.blockAt msqAX "ret_e1" = some ⟨"ret_e1", retE1Body, some "ret_a2"⟩ := by decide
theorem blockAt_retA2 : Program.blockAt msqAX "ret_a2" = some ⟨"ret_a2", retA2Body, some "ret_e2"⟩ := by decide
theorem blockAt_retE2 : Program.blockAt msqAX "ret_e2" = some ⟨"ret_e2", retE2Body, some "enq"⟩ := by decide

theorem msqAX_wf : Program.WF msqAX := by decide

section MainA

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqAX)]

local instance msqAX.env : CodeEnv := ⟨layout msqAX⟩

/-- A label's address in the laid-out `msqAX`. -/
abbrev labA (x : Label) : Int64 := (_root_.Executable.labels (layout msqAX)).label x

theorem msqAX_placed : Program.Placed msqAX "main_e" := Program.placed_of_layout msqAX_wf rfl (by decide)

/-- A data-store block: `(p, r)` is `ret_a1`'s body returning to `ret_e1`, or
`ret_a2`'s returning to `ret_e2`. -/
def AStore (p : Program) (r : Label) : Prop := (p = retA1Body ∧ r = "ret_e1") ∨ (p = retA2Body ∧ r = "ret_e2")

/-- Behind a data-store block: at `enq` with its arguments (`rdi := rbx`,
`rsi := rax`), the link at `r`, the callee-saved registers and `dmem` kept. -/
def AStorePost (r : Label) (s₀ : MachineData) (a : Int64) (s : MachineData) : Prop :=
  a = labA "enq" ∧ s.regs.get64 .r11 = (labA r).toBitVec ∧ s.regs.get64 .rdi = s₀.regs.get64 .rbx ∧
    s.regs.get64 .rsi = s₀.regs.get64 .rax ∧ s.regs.get64 .rbx = s₀.regs.get64 .rbx ∧
    s.regs.get64 .rbp = s₀.regs.get64 .rbp ∧ s.regs.get64 .r14 = s₀.regs.get64 .r14 ∧
    s.regs.get64 .r15 = s₀.regs.get64 .r15 ∧ s.dmem = s₀.dmem

set_option hygiene false in
/-- The VCs of a data-store block (`hE : E0`, `ea`: the data word's address):
the store's permission after the first silent cell and `E0` after the store
(`vc_e_strD`), carried through the silent cells behind it. -/
local macro "store_vcs" : tactic => `(tactic| (
  vcgen
  all_goals obtain ⟨rfl, rfl⟩ := ‹_ = _ ∧ _ = _›
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX,
    SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.within_step, SharedEnv.within_ok_load,
    SharedEnv.within_ok_store, SharedEnv.within_ok_rmw] at *
  case vc1 =>
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [ea]
    exact ⟨(vc_e_strD hd _ (E0.fenceC hE (by assumption)) _).1, mem_sAll8 _⟩
  case vc2 =>
    have hst := ‹(_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ ∃ ok, _)›
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hst
    obtain ⟨rfl, ⟨ok, hso⟩, -⟩ := stG hd8 hst
    rw [ea] at hso
    have hE2 := (vc_e_strD hd _ (E0.fenceC hE (by assumption)) _).2 ok _ hso
    refine ⟨?_, ?_⟩
    · simp only [AStorePost, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_true]
    · repeat (first | exact hE2 | refine E0.fenceC ?_ (by assumption))))

omit [Executable.ValidLayout (layout msqAX)] in
/-- **A data-store block** (counted `EEX P`): the node `n = rax`'s data word
`[n + 8]` by `vc_e_strD`, then `enq`'s arguments; `E0` of `n` kept. -/
theorem mainA_store (P : Params) (n : BitVec 64) (hd : ¬ P.IsW ⟨n + 8, 8⟩) (p : Program) (r : Label)
    (hp : AStore p r) (s₀ : MachineData) (g₀ : (SharedEnv.counted (EEX P)).State)
    (h0 : s₀.regs.get64 .rax = n ∧ D8 s₀.dmem ∧ E0 P n g₀.1) :
    ⦃ fun s g => s = s₀ ∧ g = g₀ ⦄ (⟨p⟩ : EnvProgram (SharedEnv.counted (EEX P)))
      ⦃ fun _ _ _ => False; fun a s g => AStorePost r s₀ a s ∧ E0 P n g.1 ⦄ := by
  obtain ⟨hax, hd8, hE⟩ := h0
  have ea : s₀.regs.get64 .rax + Int64.toBitVec 8 = n + 8 := by rw [hax]; rfl
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · unfold retA1Body; store_vcs
  · unfold retA2Body; store_vcs

/-- **`alloc` in `msqAX`** (counted `EEX P`), `R` a fence-stable predicate of
the enqueuer's state. -/
theorem allocA (P : Params) (Rn : EStateX → Prop) (hRn : ∀ σ σ', Rn σ → X64.EnvG.FenceLe σ σ' → Rn σ')
    (n : BitVec 64) :
    FunSpecPartialEnv (SharedEnv.counted (EEX P)) (labA "alloc") (AllocPreX _ (fun g => Rn g.1) n)
      (AllocPostX _ (fun g => Rn g.1) n) :=
  (allocFragX_spec _ _ (fun g g' h hle => by
      simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle
      exact hRn _ _ h hle.1) n).of_placed msqAX_placed (by decide)

/-- `main_e`'s precondition: the link `raM`, `rbx = &tail`, the bump pointer
`r14 = n1` with room for **two** nodes below `r15`, `dmem` empty, `E0` of
`n1`. -/
def MainAPreX (P : Params) (raM : Int64) (s : MachineData) (σ : (SharedEnv.counted (EEX P)).State) : Prop :=
  s.regs.get64 .r11 = raM.toBitVec ∧ s.regs.get64 .rbx = P.t ∧ s.regs.get64 .r14 = P.n1 ∧
    s.regs.get64 .r14 + 16 ≤ s.regs.get64 .r15 ∧ P.n1 + 16 + 16 ≤ s.regs.get64 .r15 ∧ D8 s.dmem ∧ E0 P P.n1 σ.1

/-- **`main_e`'s run** (counted `EEX P`, partial): every run that stops is at
the link `raM` with `ComE`. The second `alloc` returns `n1 + 16 = n2`
(`hn2`); the data words `[n1 + 8]`, `[n2 + 8]` are not queue words. -/
theorem mainA_specX (P : Params) (hL : QLocs P) (hn2 : P.n2 = P.n1 + 16) (hd1 : ¬ P.IsW ⟨P.n1 + 8, 8⟩)
    (hd2 : ¬ P.IsW ⟨P.n2 + 8, 8⟩) (raM : Int64) :
    ∀ s g, MainAPreX P raM s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EEX P))) (fun x => x.1.2 = raM ∧ ComE P x.2.1)
        ((s, labA "main_e"), g) := by
  have hpl : Program.PlacedIn msqAX := msqAX_placed.toPlacedIn
  have hE : ∀ n, FunSpecPartialEnv (SharedEnv.counted (EEX P)) (labA "enq") (EnqPre P n) (EnqPost P n) :=
    fun n => (enq_fragXR P n hL).of_placed msqAX_placed (by decide)
  rintro s g ⟨h11, hbx, h14, hr1, hr2, hd8, hE0⟩
  -- `main_e`: the link into `rbp`, `jmp alloc`
  refine Safely.blockAt hpl blockAt_mainA (X := fun a s₁ => a = labA "alloc" ∧
      s₁.regs.get64 .r11 = (labA "ret_a1").toBitVec ∧ s₁.regs.get64 .rbp = raM.toBitVec ∧
      s₁.regs.get64 .rbx = P.t ∧ s₁.regs.get64 .r14 = P.n1 ∧ s₁.regs.get64 .r15 = s.regs.get64 .r15 ∧
      s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainABody]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h14, h11, and_true]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1bp, h1bx, h1r14, h1r15, h1dm⟩ hle₁
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₁
  -- `alloc`: node 1
  refine (allocA P (E0 P P.n1) (fun _ _ h hf => h.fence hf) P.n1).jcall (ra := labA "ret_a1")
    ⟨h1r11, h1r14, by rw [h1r14, h1r15, ← h14]; exact hr1, hE0.fence hle₁.1⟩
    fun s₂ g₂ ⟨h2ax, h2r14, ⟨h2bx, h2bp, _, _, h2r15, h2dm⟩, hE2⟩ => ?_
  -- node 1's data word, `enq`'s arguments
  refine Safely.blockAtEnv hpl blockAt_retA1 (mainA_store P P.n1 hd1 _ _ (.inl ⟨rfl, rfl⟩) s₂ g₂
    ⟨h2ax, by rw [h2dm, h1dm]; exact hd8, hE2⟩) ?_
  rintro a s₃ g₃ ⟨⟨rfl, h3r11, h3di, h3si, h3bx, h3bp, h3r14, h3r15, h3dm⟩, hE3⟩
  -- `enq`: node 1
  refine (hE P.n1).jcall (ra := labA "ret_e1") ⟨h3r11, by rw [h3di, h2bx, h1bx], by rw [h3si, h2ax],
    by rw [h3dm, h2dm, h1dm]; exact hd8, hE3⟩ fun s₄ g₄ ⟨⟨h4bx, h4bp, _, _, h4r14, h4r15, h4dm⟩, y3, hLk⟩ => ?_
  -- `ret_e1`: `jmp alloc`
  refine Safely.blockAt hpl blockAt_retE1 (X := fun a s₅ => a = labA "alloc" ∧
      s₅.regs.get64 .r11 = (labA "ret_a2").toBitVec ∧ s₅.regs.get64 .rbp = s₄.regs.get64 .rbp ∧
      s₅.regs.get64 .rbx = s₄.regs.get64 .rbx ∧ s₅.regs.get64 .r14 = s₄.regs.get64 .r14 ∧
      s₅.regs.get64 .r15 = s₄.regs.get64 .r15 ∧ s₅.dmem = s₄.dmem) ?_ ?_
  · simp only [retE1Body]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_true]
  rintro a s₅ g₅ ⟨rfl, h5r11, h5bp, h5bx, h5r14, h5r15, h5dm⟩ hle₅
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₅
  -- `alloc`: node 2, at `n1 + 16`
  have e14 : s₅.regs.get64 .r14 = P.n2 := by rw [h5r14, h4r14, h3r14, h2r14, hn2]
  have e15 : s₅.regs.get64 .r15 = s.regs.get64 .r15 := by rw [h5r15, h4r15, h3r15, h2r15, h1r15]
  refine (allocA P (E0 P P.n2) (fun _ _ h hf => h.fence hf) P.n2).jcall (ra := labA "ret_a2")
    ⟨h5r11, e14, by rw [e14, e15, hn2]; exact hr2, (Linked.next hL hLk).fence hle₅.1⟩
    fun s₆ g₆ ⟨h6ax, _, ⟨h6bx, h6bp, _, _, _, h6dm⟩, hE6⟩ => ?_
  -- node 2's data word
  refine Safely.blockAtEnv hpl blockAt_retA2 (mainA_store P P.n2 hd2 _ _ (.inr ⟨rfl, rfl⟩) s₆ g₆
    ⟨h6ax, by rw [h6dm, h5dm, h4dm, h3dm, h2dm, h1dm]; exact hd8, hE6⟩) ?_
  rintro a s₇ g₇ ⟨⟨rfl, h7r11, h7di, h7si, -, h7bp, -, -, h7dm⟩, hE7⟩
  -- `enq`: node 2
  refine (hE P.n2).jcall (ra := labA "ret_e2") ⟨h7r11, by rw [h7di, h6bx, h5bx, h4bx, h3bx, h2bx, h1bx],
    by rw [h7si, h6ax], by rw [h7dm, h6dm, h5dm, h4dm, h3dm, h2dm, h1dm]; exact hd8, hE7⟩
    fun s₈ g₈ ⟨⟨_, h8bp, _, _, _, _, _⟩, y3', hLk'⟩ => ?_
  -- `ret_e2`: `jmp *%rbp`
  refine Safely.blockAt hpl blockAt_retE2 (X := fun a _ => a = Int64.ofBitVec (s₈.regs.get64 .rbp)) ?_ ?_
  · simp only [retE2Body]
    vcgen
    case vc1 s' hs => subst hs; rfl
  rintro a s₉ g₉ rfl hle₉
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₉
  exact Safely.fold (.inl ⟨ofBitVec_reg (by rw [h8bp, h7bp, h6bp, h5bp, h4bp, h3bp, h2bp, h1bp]),
    (hLk'.fence hle₉.1).1⟩)

end MainA

/-! ## The purity twin (counted `EnvRT sAll`) -/

/-- `enq`'s twin pre: the link `r11 = ra`, `dmem` empty. -/
def EnqPreR (ra : Int64) (t : MachineData) (_ : (SharedEnv.counted (EnvRT sAll)).State) : Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ D8 t.dmem

/-- `enq`'s twin post: the frame kept, `dmem` empty. -/
def EnqPostR (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EnvRT sAll)).State) (s : MachineData)
    (_ : (SharedEnv.counted (EnvRT sAll)).State) : Prop :=
  Saved t s ∧ D8 s.dmem

/-- `enq`'s twin table: the link, the frame, `dmem` empty. -/
abbrev enqTableR (ra : Int64) (t : MachineData) (_ : (SharedEnv.counted (EnvRT sAll)).State) :
    Label → MachineData → (SharedEnv.counted (EnvRT sAll)).State → Prop :=
  fun _ s _ => s.regs.get64 .r11 = ra.toBitVec ∧ Saved t s ∧ D8 s.dmem

set_option maxHeartbeats 4000000 in
/-- **`enq`'s twin** (the x64 MS queue pilot's `enqFrag`, every placement): every access is
admitted by the all-release environment (`dmem` empty; the `lock cmpxchgq`s
are releases), and `enq` returns to its link with the frame kept. -/
theorem enq_pureX : FragSpecEnv (SharedEnv.counted (EnvRT sAll)) enqFrag "enq" EnqPreR EnqPostR := by
  refine FragSpecEnv.of_cfg enqTableR rfl (by decide)
    (fun ra t g ⟨h1, h2⟩ => ⟨h1, Saved.refl t, h2⟩) ?_
  intro _
  rintro ra t g -
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : (_ ∧ _) ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨h11, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hd8⟩, rfl, rfl⟩ := hx
  all_goals first
    | exact hd8 _
    | exact hd8
    | (refine ⟨⟨?_, mem_sAll8 _⟩, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | (dsimp only
       simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
       first
         | exact .inr ⟨ofBitVec_reg h11, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hd8⟩
         | exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨h11, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hd8⟩,
             .inl (by decide)⟩)
         | (refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨h11, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hd8⟩,
             .inr fun ⟨_, hg⟩ => ?_⟩)
            subst hg; cnt_all; omega))
    | skip
  all_goals done

section PureA

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqAX)]

local instance msqAX.envP : CodeEnv := ⟨layout msqAX⟩

set_option hygiene false in
/-- The VCs of a data-store block in the twin: the store admitted, the frame. -/
local macro "store_pure_vcs" : tactic => `(tactic| (
  vcgen
  all_goals obtain ⟨rfl, rfl⟩ := ‹_ = _ ∧ _ = _›
  all_goals first
    | exact hd8 _
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | (have hst := ‹(_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ ∃ ok, _)›
       obtain ⟨rfl, -, -⟩ := stG hd8 hst
       simp only [AStorePost, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_true])))

omit [Executable.ValidLayout (layout msqAX)] in
/-- **A data-store block is pure** (counted `EnvRT sAll`): the store is
admitted (`dmem` empty; a release under `Arch.tso`), then `enq`'s arguments. -/
theorem mainA_store_pure (p : Program) (r : Label) (hp : AStore p r) (s₀ : MachineData)
    (g₀ : (SharedEnv.counted (EnvRT sAll)).State) (hd8 : D8 s₀.dmem) :
    ⦃ fun s g => s = s₀ ∧ g = g₀ ⦄ (⟨p⟩ : EnvProgram (SharedEnv.counted (EnvRT sAll)))
      ⦃ fun _ _ _ => False; fun a s _ => AStorePost r s₀ a s ⦄ := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · unfold retA1Body; store_pure_vcs
  · unfold retA2Body; store_pure_vcs

set_option hygiene false in
/-- A twin block without shared access, by one `vcgen` (`Skips`: the state
is unchanged). -/
local macro "pblock" "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  vcgen
  all_goals obtain ⟨rfl, rfl⟩ := ‹_ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_true, $ids,*]))

/-- `main_e`'s twin pre: the link `raM`, room for two nodes from `r14` below
`r15`, `dmem` empty. -/
def MainAPreR (raM : Int64) (s : MachineData) (_ : (SharedEnv.counted (EnvRT sAll)).State) : Prop :=
  s.regs.get64 .r11 = raM.toBitVec ∧ s.regs.get64 .r14 + 16 ≤ s.regs.get64 .r15 ∧
    s.regs.get64 .r14 + 16 + 16 ≤ s.regs.get64 .r15 ∧ D8 s.dmem

/-- **`main_e`'s twin** (counted `EnvRT sAll`, partial): every run that stops
is at the link `raM`. -/
theorem mainA_pureX (raM : Int64) :
    ∀ s g, MainAPreR raM s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll))) (fun x => x.1.2 = raM)
        ((s, labA "main_e"), g) := by
  have hpl : Program.PlacedIn msqAX := msqAX_placed.toPlacedIn
  have hA : ∀ n, FunSpecPartialEnv (SharedEnv.counted (EnvRT sAll)) (labA "alloc") (AllocPreX _ (fun _ => True) n)
      (AllocPostX _ (fun _ => True) n) :=
    fun n => (allocFragX_spec_skips _ _ n).of_placed msqAX_placed (by decide)
  have hE : FunSpecPartialEnv (SharedEnv.counted (EnvRT sAll)) (labA "enq") EnqPreR EnqPostR :=
    enq_pureX.of_placed msqAX_placed (by decide)
  rintro s g ⟨h11, hr1, hr2, hd8⟩
  refine Safely.blockAtEnv hpl blockAt_mainA (X := fun a s₁ _ => a = labA "alloc" ∧
      s₁.regs.get64 .r11 = (labA "ret_a1").toBitVec ∧ s₁.regs.get64 .rbp = raM.toBitVec ∧
      s₁.regs.get64 .r14 = s.regs.get64 .r14 ∧ s₁.regs.get64 .r15 = s.regs.get64 .r15 ∧ s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainABody]
    pblock [h11]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1bp, h1r14, h1r15, h1dm⟩
  refine (hA _).jcall (ra := labA "ret_a1") ⟨h1r11, rfl, by rw [h1r14, h1r15]; exact hr1, trivial⟩
    fun s₂ g₂ ⟨h2ax, h2r14, ⟨_, h2bp, _, _, h2r15, h2dm⟩, _⟩ => ?_
  refine Safely.blockAtEnv hpl blockAt_retA1 (mainA_store_pure _ _ (.inl ⟨rfl, rfl⟩) s₂ g₂
    (by rw [h2dm, h1dm]; exact hd8)) ?_
  rintro a s₃ g₃ ⟨rfl, h3r11, -, -, -, h3bp, h3r14, h3r15, h3dm⟩
  refine hE.jcall (ra := labA "ret_e1") ⟨h3r11, by rw [h3dm, h2dm, h1dm]; exact hd8⟩
    fun s₄ g₄ ⟨⟨_, h4bp, _, _, h4r14, h4r15, h4dm⟩, _⟩ => ?_
  refine Safely.blockAtEnv hpl blockAt_retE1 (X := fun a s₅ _ => a = labA "alloc" ∧
      s₅.regs.get64 .r11 = (labA "ret_a2").toBitVec ∧ s₅.regs.get64 .rbp = s₄.regs.get64 .rbp ∧
      s₅.regs.get64 .r14 = s₄.regs.get64 .r14 ∧ s₅.regs.get64 .r15 = s₄.regs.get64 .r15 ∧ s₅.dmem = s₄.dmem) ?_ ?_
  · simp only [retE1Body]
    pblock []
  rintro a s₅ g₅ ⟨rfl, h5r11, h5bp, h5r14, h5r15, h5dm⟩
  have e14 : s₅.regs.get64 .r14 = s.regs.get64 .r14 + 16 := by rw [h5r14, h4r14, h3r14, h2r14, h1r14]
  have e15 : s₅.regs.get64 .r15 = s.regs.get64 .r15 := by rw [h5r15, h4r15, h3r15, h2r15, h1r15]
  refine (hA _).jcall (ra := labA "ret_a2") ⟨h5r11, rfl, by rw [e14, e15]; exact hr2, trivial⟩
    fun s₆ g₆ ⟨_, _, ⟨_, h6bp, _, _, _, h6dm⟩, _⟩ => ?_
  refine Safely.blockAtEnv hpl blockAt_retA2 (mainA_store_pure _ _ (.inr ⟨rfl, rfl⟩) s₆ g₆
    (by rw [h6dm, h5dm, h4dm, h3dm, h2dm, h1dm]; exact hd8)) ?_
  rintro a s₇ g₇ ⟨rfl, h7r11, -, -, -, h7bp, -, -, h7dm⟩
  refine hE.jcall (ra := labA "ret_e2") ⟨h7r11, by rw [h7dm, h6dm, h5dm, h4dm, h3dm, h2dm, h1dm]; exact hd8⟩
    fun s₈ g₈ ⟨⟨_, h8bp, _, _, _, _, _⟩, _⟩ => ?_
  refine Safely.blockAtEnv hpl blockAt_retE2 (X := fun a _ _ => a = Int64.ofBitVec (s₈.regs.get64 .rbp)) ?_ ?_
  · simp only [retE2Body]
    pblock []
  rintro a s₉ g₉ rfl
  exact Safely.fold (.inl (ofBitVec_reg (by rw [h8bp, h7bp, h6bp, h5bp, h4bp, h3bp, h2bp, h1bp])))

end PureA

end Kraken.Promising.Lower.MsqAllocX
