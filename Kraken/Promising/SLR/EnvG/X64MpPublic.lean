/-
**x64 message passing under `Arch.tso`, proved on `EnvG`**: `x64_mp_public`, the
shape of `MpPublic.mp_public` for the x64 writer `mov [d], 42; mov [f], 1`
and reader `spin: mov eax, [f]; cmp eax, 0; je spin; mov ebx, [d]`, for all
layouts.

- **Start** (`StartWX`, `StartRX`): the laid-out program at its first
  instruction, no declarations, `rdi = f`, `rsi = d`, and neither word's
  bytes in the private memory (`Split [(f, 4), (d, 4)]`, the x64 link's side
  condition; it gives the `Mem.loadInt … = none` facts of the `vcgen`
  preconditions).
- **The rules' invariants at the start** (`invWX_init`, `invRX_init`):
  `invGX_init` at `σInitX` with `mpRes`/`mpGhost`, `QX64` from the `vcgen`
  proofs by `qx64_of_partialTripleEnv`.
- **`NPSafe`** (`x64_mp_npSafe`): `NPSafe.of_ruleRX` at the two rules.
- **Scope and purity**: `final_of_relPureSafelyQX_tso` with one all-release
  specification per thread (`EnvG/X64MpRelPure.lean`): `NTFree Arch.tso` and
  purity at once.
- **Initial erasure and final argument**: `erase_mpInit`, `mp_final`
  (`EnvG/X64MpSpec.lean`).
-/
import Kraken.Promising.SLR.EnvG.X64MpLink
import Kraken.Promising.SLR.EnvG.X64MpRelPure

namespace Kraken.Promising.X64.EnvG.MpPublic

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure

/-! ## The start -/

section Start

variable [layout : _root_.Layout]

/-- The x64 writer at its start, with flag address `f` and data address `d`. -/
structure StartWX (f d : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout mpWriterX
  decls : s.decls = {}
  endPc : s.endPc = (layout mpWriterX).addrOf mpWriterX.length
  pc : s.st.2 = (layout mpWriterX).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = f
  rsi : s.st.1.regs.get64 .rsi = d
  split : Split [(f, 4), (d, 4)] s.st.1.dmem

/-- The x64 reader at its start (the label `spin`), as `StartWX`. -/
structure StartRX (f d : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout mpReaderX
  decls : s.decls = {}
  endPc : s.endPc = (layout mpReaderX).addrOf mpReaderX.length
  pc : s.st.2 = (layout mpReaderX).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = f
  rsi : s.st.1.regs.get64 .rsi = d
  split : Split [(f, 4), (d, 4)] s.st.1.dmem

omit layout in
theorem split_df {f d : BitVec 64} {m : DataMem} (h : Split [(f, 4), (d, 4)] m) : Mem.loadInt m f 4 = none :=
  h.loadInt_none (by simp) (by decide) (by decide)

omit layout in
theorem split_dd {f d : BitVec 64} {m : DataMem} (h : Split [(f, 4), (d, 4)] m) : Mem.loadInt m d 4 = none :=
  h.loadInt_none (by simp) (by decide) (by decide)

/-- The parameters with the ghost token chosen. -/
def ghostParams (f d : BitVec 64) : Params where
  f := f
  d := d
  W := ⟨0, 5⟩

omit layout in
theorem ghostParams_mpLocs {f d : BitVec 64} (hfd : f ≠ d) : MpLocs (ghostParams f d) where
  fd := hfd
  wf h := by have := congrArg Loc.bytes h; simp [ghostParams] at this
  wd h := by have := congrArg Loc.bytes h; simp [ghostParams] at this

variable {f d : BitVec 64} {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- **The x64 writer's initial invariant** (thread `0`). -/
theorem invWX_init [Executable.ValidLayout (layout mpWriterX)] (hfd : f ≠ d) (hW : StartWX f d sW) :
    (mpRuleW_envGX (ghostParams f d) (ghostParams_mpLocs hfd) 0 1).Inv True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 0) (mpGhost (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout mpWriterX⟩
  have hL := ghostParams_mpLocs hfd
  refine invGX_init (s := sW) rfl rfl (qx64_of_partialTripleEnv (mpWriterX_envG _ hL 0).partial rfl hW.exe
    hW.decls hW.endPc hW.pc hW.split ⟨hW.rdi, hW.rsi, split_df hW.split, split_dd hW.split, ⟨mpGhost_rel_Fl, fun v => ?_⟩, ?_⟩)
  · show Pred.Pure ((mpGhost _).rel _) v
    rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v
  · simp only [σInitX, Own0, mpRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
    exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

/-- **The x64 reader's initial invariant** (thread `1`). -/
theorem invRX_init [Executable.ValidLayout (layout mpReaderX)] (hfd : f ≠ d) (hR : StartRX f d sR) :
    (mpRuleR_envGX (ghostParams f d) (ghostParams_mpLocs hfd) 1).Inv True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 1) (mpGhost (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout mpReaderX⟩
  refine invGX_init (s := sR) rfl rfl (qx64_of_partialTripleEnv (mpReaderX_envGP _ 1).uncount rfl hR.exe
    hR.decls hR.endPc hR.pc hR.split
    ⟨0, ⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩, ⟨mpGhost_rel_Fl, 0, Nat.zero_lt_one, rfl, ?_⟩, ?_⟩)
  · simp [σInitX, mpRes, readerRes]
  · simp [σInitX, Views.getFwd]

end Start

/-! ## `NPSafe` -/

/-- **The `NPSafe` side of Theorem 1′ for x64 MP on `EnvG`.** -/
theorem x64_mp_npSafe (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] {f d : BitVec 64} (hfd : f ≠ d) {sW sR : isa.State}
    {initMem : List (Loc × Val)} (hW : StartWX (layout := lW) f d sW) (hR : StartRX (layout := lR) f d sR) :
    ∀ tid, tid < [sW, sR].length → ∀ n m, NPSafe (model isa) Arch.tso (MpPost (ghostParams f d) 1) tid n m True
      (Config.init [sW, sR] initMem) (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) tid)
      (mpGhost (ghostParams f d)) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invWX_init (layout := lW) hfd hW)
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invRX_init (layout := lR) hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## Scope and purity -/

/-- The MP threads' all-release specifications: the writer (layout `lW`) at
thread `0`, the reader (layout `lR`) elsewhere. -/
def mpNoNTSpec (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] (f d : BitVec 64) :
    Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 => RelPureSpecQX.ofProgram (layout := lW) [(f, 4), (d, 4)] (mpS_le16 ⟨f, d, ⟨0, 5⟩⟩) mpWriterX
      fun _ _ => True
  | _ + 1 => RelPureSpecQX.ofProgram (layout := lR) [(f, 4), (d, 4)] (mpS_le16 ⟨f, d, ⟨0, 5⟩⟩) mpReaderX
      fun _ _ => ∃ _ : Nat, True

/-- **The all-release specifications hold at the MP start states.** -/
theorem mpNoNTSpec_init (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] {f d : BitVec 64} {sW sR : isa.State}
    (hW : StartWX (layout := lW) f d sW) (hR : StartRX (layout := lR) f d sR) :
    ∀ tid s, [sW, sR][tid]? = some s → (mpNoNTSpec lW lR f d tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hsp⟩ := hW
    letI : CodeEnv := ⟨lW mpWriterX⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lW) (mpWriterX_noNT (layout := lW) f d).partial rfl
      he hds hend hpc hsp ⟨hx0, hx1⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hsp⟩ := hR
    letI : CodeEnv := ⟨lR mpReaderX⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lR) (mpReaderX_noNT (layout := lR) f d).uncount rfl
      he hds hend hpc hsp ⟨0, hx0, hx1, split_df hsp⟩
  | _ + 2, _, hs => by cases hs

/-! ## The theorem -/

/-- **Message passing for x64 under `Arch.tso`, proved on `EnvG`** (the shape
of `MpPublic.mp_public`).

For valid layouts `lW` of `mpWriterX` and `lR` of `mpReaderX` and addresses
`f ≠ d`: if thread `0` is the writer and thread `1` the reader, each at its
start with `rdi = f`, `rsi = d` and neither word in its private memory
(`StartWX`, `StartRX`), and the initial memory has the flag word `⟨f, 4⟩` at
`0`, then every configuration `Reachable` under `Arch.tso` that is final has
the reader's `ebx` at `42` and the data word `⟨d, 4⟩` at `42`.

As for `mp_public`: only final configurations are constrained (a reader
spinning forever never becomes final; no fairness), `f ≠ d` does not exclude
overlapping words, and faults are not covered (`mpRuleW_envGX_noFault`,
`mpRuleR_envGX_noFault` are the rules' no-fault facts). -/
theorem x64_mp_public {fuel : Nat} (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lR mpReaderX)] (f d : BitVec 64) (hfd : f ≠ d)
    {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartWX (layout := lW) f d sW) (hR : StartRX (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 42#128 :=
  final_of_relPureSafelyQX_tso fuel (B := MpPost (ghostParams f d) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal ⟨d, 4⟩ = 42#128)
    (erase_mpInit _ _ hF0) pend_mpGhost (mpNoNTSpec lW lR f d) (mpNoNTSpec_init lW lR hW hR)
    (x64_mp_npSafe lW lR hfd hW hR) hc hf
    fun _ _ E' hle hsize hB => mp_final E' hf hsize (by rw [hle.rel]; exact mpGhost_rel_Fl) hB

end Kraken.Promising.X64.EnvG.MpPublic
