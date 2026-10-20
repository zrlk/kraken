/-
**Demonstration: the x64 MS queue pilot's `msqXR_promising` with
`main` and `pure` from fragment specs.** ISA: x64;
machine: the executable Promising machine (`Reachable Arch.tso`) through the
x64 kit (`KitX.lower_promising_x64`).

The x64 MS queue pilot (`Lower/MsqXR*.lean`) proved each thread's `main` (`mainE_specXR`,
`mainD_specXR`) and purity twin (`msqXR_pureE`/`D`) at its own text `msqXR`
(`labX`, `msqXR_placed`, the link at `labX "done"`). Here the same runs are
**placement-generic fragment specs** (`Lower/FragSpecCallsX64.lean`):

- `mainE_fragX`: `FragSpecEnvL (counted (EEX P)) [mainETxt, enqFrag]
  "main_e" (MainEPre P) _` (two link-register calls of
  `enq_fragXR`, return to the link `ra`), and `mainD_fragX` likewise over
  `[mainDTxt, deqFrag]` with `deq_fragXR`;
- `pureE_fragX`/`pureD_fragX`: the relPure twins as `FragSpecEnv`s over
  `fragE`/`fragD` in counted `EnvRT sAll`, the link `ra` generic.

They feed `KitX.LowerStaticX.ofFragPure` and `KitX.LowerThreadX.ofFrag`
(`Lower/KitFragX.lean`) at `layout msqXR` with the return address read as
`labX "done"`; the threads' static fields (`hB_E`/`hB_D`, `msqXR_stuck`,
`msqXR_phase1FX`) are the x64 MS queue pilot's. `msqXR_promising_viaFragKitX` has the
statement of `MsqXR.msqXR_promising` (checked by `rfl` below).

The block lemmas are re-stated at the fragments `mainETxt`/`mainDTxt`
(whose last block does not fall through), and the twin tactics of
`MsqXRPure.lean` are local there, so they are copied here verbatim
(`twin_land`, `twin_cases`).
-/
import Kraken.Promising.Lower.MsqXRWhole
import Kraken.Promising.Lower.KitFragX

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.FragKitX

open Kraken.Promising.Lower.MsqXR
open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 split_sAll mem_sAll8 EnvRT)
open Kraken.Promising.Lower.KitX (LowerStaticX LowerThreadX lower_promising_x64)
open Kraken.Promising.Lower.PilotXR (D8 ofBitVec_reg)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- A label's address in the ambient code. -/
abbrev labC [CodeEnv] (x : Label) : Int64 := (_root_.Executable.labels cenv).label x

/-! ## `main_e`, `main_d` as fragment specs -/

theorem blockAt_mainE' : Program.blockAt mainETxt "main_e" = some ⟨"main_e", mainEBody, some "ret_e1"⟩ := by
  decide
theorem blockAt_retE1' : Program.blockAt mainETxt "ret_e1" = some ⟨"ret_e1", retE1Body, some "ret_e2"⟩ := by
  decide
theorem blockAt_retE2' : Program.blockAt mainETxt "ret_e2" = some ⟨"ret_e2", retE2Body, none⟩ := by decide
theorem blockAt_mainD' : Program.blockAt mainDTxt "main_d" = some ⟨"main_d", mainDBody, some "ret_d1"⟩ := by
  decide
theorem blockAt_retD1' : Program.blockAt mainDTxt "ret_d1" = some ⟨"ret_d1", retD1Body, some "ret_d2"⟩ := by
  decide
theorem blockAt_retD2' : Program.blockAt mainDTxt "ret_d2" = some ⟨"ret_d2", retD2Body, none⟩ := by decide

/-- **`main_e`'s spec, every placement** (counted `EEX`): from `MainEPre` at
the link `ra`, two calls of `enq` (`enq_fragXR`), return to `ra` with `ComE`. -/
theorem mainE_fragX (P : Params) (hL : QLocs P) :
    FragSpecEnvL (SharedEnv.counted (EEX P)) [mainETxt, enqFrag] "main_e" (MainEPre P)
      (fun _ _ _ _ σ => ComE P σ.1) := by
  refine ⟨fun hpls raM s g ⟨h11, hbx, h12, h13, hd8, hE0⟩ => ?_⟩
  have hpl : Program.PlacedIn mainETxt := hpls _ List.mem_cons_self
  have hE : ∀ n, FunSpecPartialEnv (SharedEnv.counted (EEX P)) (labC "enq") (EnqPre P n) (EnqPost P n) :=
    fun n => (enq_fragXR P n hL).at (hpls _ (List.mem_cons_of_mem _ List.mem_cons_self))
  refine Safely.blockAtLabel hpl blockAt_mainE' (X := fun a s₁ => a = labC "enq" ∧
      s₁.regs.get64 .r11 = (labC "ret_e1").toBitVec ∧ s₁.regs.get64 .rdi = P.t ∧ s₁.regs.get64 .rsi = P.n1 ∧
      s₁.regs.get64 .rbp = raM.toBitVec ∧ s₁.regs.get64 .rbx = P.t ∧ s₁.regs.get64 .r13 = P.n2 ∧
      s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainEBody]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h12, h11, h13, and_true]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1di, h1si, h1bp, h1bx, h113, h1dm⟩ hle₁
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₁
  refine (hE P.n1).jcallLink (ra := labC "ret_e1") ⟨h1r11, h1di, h1si, h1dm ▸ hd8, hE0.fence hle₁.1⟩
    fun s₂ g₂ ⟨⟨h2bx, h2bp, _, h213, _, _, h2dm⟩, y3, hLk⟩ => ?_
  refine Safely.blockAtLabel hpl blockAt_retE1' (X := fun a s₃ => a = labC "enq" ∧
      s₃.regs.get64 .r11 = (labC "ret_e2").toBitVec ∧ s₃.regs.get64 .rdi = P.t ∧ s₃.regs.get64 .rsi = P.n2 ∧
      s₃.regs.get64 .rbp = s₂.regs.get64 .rbp ∧ s₃.dmem = s₂.dmem) ?_ ?_
  · simp only [retE1Body]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h2bx, h1bx, h213, h113, and_true]
  rintro a s₃ g₃ ⟨rfl, h3r11, h3di, h3si, h3bp, h3dm⟩ hle₃
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₃
  refine (hE P.n2).jcallLink (ra := labC "ret_e2")
    ⟨h3r11, h3di, h3si, by rw [h3dm, h2dm, h1dm]; exact hd8, (Linked.next hL hLk).fence hle₃.1⟩
    fun s₄ g₄ ⟨⟨_, h4bp, _, _, _, _, _⟩, y3', hLk'⟩ => ?_
  refine Safely.blockAtLabel hpl blockAt_retE2' (X := fun a _ => a = Int64.ofBitVec (s₄.regs.get64 .rbp)) ?_ ?_
  · simp only [retE2Body]
    vcgen
    case vc1 s' hs => subst hs; rfl
  rintro a s₅ g₅ rfl hle₅
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₅
  exact Safely.fold (.inl ⟨ofBitVec_reg (by rw [h4bp, h3bp, h2bp, h1bp]), (hLk'.fence hle₅.1).1⟩)

/-- **`main_d`'s spec, every placement** (counted `EDX`): from `MainDPre` at
the link `ra`, two calls of `deq` (`deq_fragXR`), return to `ra` with `Dn` of
`r12`, `r13`. -/
theorem mainD_fragX (P : Params) (hL : QLocs P) (hpt : P.trk = false) :
    FragSpecEnvL (SharedEnv.counted (EDX P)) [mainDTxt, deqFrag] "main_d" (MainDPre P)
      (fun _ _ _ s σ => Dn P (s.regs.get64 .r12) (s.regs.get64 .r13) σ.1) := by
  refine ⟨fun hpls raM s g ⟨h11, hbx, h14, hd8, hC⟩ => ?_⟩
  have hpl : Program.PlacedIn mainDTxt := hpls _ List.mem_cons_self
  have hD : FunSpecPartialEnv (SharedEnv.counted (EDX P)) (labC "deq") (DeqPre P) (DeqPost P) :=
    (deq_fragXR P hL hpt).at (hpls _ (List.mem_cons_of_mem _ List.mem_cons_self))
  refine Safely.blockAtLabel hpl blockAt_mainD' (X := fun a s₁ => a = labC "deq" ∧
      s₁.regs.get64 .r11 = (labC "ret_d1").toBitVec ∧ s₁.regs.get64 .rdi = P.h ∧ s₁.regs.get64 .rsi = P.t ∧
      s₁.regs.get64 .rbp = raM.toBitVec ∧ s₁.regs.get64 .rbx = P.h ∧ s₁.regs.get64 .r14 = P.t ∧
      s₁.dmem = s.dmem) ?_ ?_
  · simp only [mainDBody]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h14, h11, and_true]
  rintro a s₁ g₁ ⟨rfl, h1r11, h1di, h1si, h1bp, h1bx, h114, h1dm⟩ hle₁
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₁
  refine hD.jcallLink (ra := labC "ret_d1") ⟨h1r11, h1di, h1si, h1dm ▸ hd8, hC.fence hle₁.1⟩
    fun s₂ g₂ ⟨⟨h2bx, h2bp, _, _, h214, _, h2dm⟩, hC2, hF2, _⟩ => ?_
  refine Safely.blockAtLabel hpl blockAt_retD1' (X := fun a s₃ => a = labC "deq" ∧
      s₃.regs.get64 .r11 = (labC "ret_d2").toBitVec ∧ s₃.regs.get64 .rdi = P.h ∧ s₃.regs.get64 .rsi = P.t ∧
      s₃.regs.get64 .rbp = s₂.regs.get64 .rbp ∧ s₃.regs.get64 .r12 = s₂.regs.get64 .rax ∧
      s₃.dmem = s₂.dmem) ?_ ?_
  · simp only [retD1Body]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h2bx, h1bx, h214, h114, and_true]
  rintro a s₃ g₃ ⟨rfl, h3r11, h3di, h3si, h3bp, h312, h3dm⟩ hle₃
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₃
  refine hD.jcallLink (ra := labC "ret_d2")
    ⟨h3r11, h3di, h3si, by rw [h3dm, h2dm, h1dm]; exact hd8, hC2.fence hle₃.1⟩
    fun s₄ g₄ ⟨⟨_, h4bp, h412, _, _, _, _⟩, hC4, _, hD4⟩ => ?_
  refine Safely.blockAtLabel hpl blockAt_retD2' (X := fun a s₅ => a = Int64.ofBitVec (s₄.regs.get64 .rbp) ∧
      s₅.regs.get64 .r12 = s₄.regs.get64 .r12 ∧ s₅.regs.get64 .r13 = s₄.regs.get64 .rax) ?_ ?_
  · simp only [retD2Body]
    vcgen
    case vc1 s' hs =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, and_true]
  rintro a s₅ g₅ ⟨rfl, h512, h513⟩ hle₅
  simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX] at hle₅
  refine Safely.fold (.inl ⟨ofBitVec_reg (by rw [h4bp, h3bp, h2bp, h1bp]), ?_⟩)
  rw [h512, h513, h412, h312]
  exact Dn.fence (show Dn P _ _ _ from ⟨hC4, hD4 _ ((yok_first _).fence hF2 hle₃.1)⟩) hle₅.1

/-! ## The relPure twins as fragment specs -/

set_option hygiene false in
/-- Land on a table label, or exit (`MsqXRPure.lean`'s local tactic, verbatim). -/
local macro "twin_land" : tactic => `(tactic| (
  first
    | exact .inr (ofBitVec_reg hT)
    | exact .inr (ofBitVec_reg hT.2)
    | (refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, ?_⟩, ?_⟩)
       · have hT' := hT; simp only [Reg64s.get64] at hT'
         simp (config := { decide := true }) [twinT, hT, hT']
       · first | exact .inl (by decide) | exact .inr fun ⟨_, hg⟩ => by subst hg; cnt_all; omega)))

set_option hygiene false in
/-- Every VC of a twin (`MsqXRPure.lean`'s local tactic, verbatim). -/
local macro "twin_cases" : tactic => `(tactic| (
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : twinT _ _ _ _ _ _ _ _ ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨hd8, hT⟩, rfl, rfl⟩ := hx
  all_goals simp only [↓reduceIte, String.reduceEq, or_false, false_or, or_self] at hT
  all_goals first
    | exact hd8 _
    | (refine ⟨⟨?_, mem_sAll8 _⟩, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | (try dsimp only
       try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
       first
         | twin_land
         | (rcases hT.1 with h | h <;> rw [ofBitVec_reg h] <;> twin_land))
    | skip))

/-- The twins' precondition: `dmem` empty, the link at `ra`. -/
def PreRF (ra : Int64) (s : MachineData) (_ : (SharedEnv.counted (EnvRT sAll)).State) : Prop :=
  D8 s.dmem ∧ s.regs.get64 .r11 = ra.toBitVec

set_option hygiene false in
/-- A twin's proof at the link `ra`: the fragment `f`, the `main` `m` with
returns `r1`, `r2` (`MsqXRPure.lean`'s `twin_run`, `labX "done"` → `ra`). -/
local macro "twin_runF" f:ident m:str r1:str r2:str "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
  refine ⟨fun hpl ra s g ⟨hd8, h11⟩ => ?_⟩
  refine (cfgEnv_partial_fun (p := $f) (env := SharedEnv.counted (EnvRT sAll)) (E := fun a _ _ => a = ra)
    (fun lb s _ => twinT $m $r1 $r2 ra.toBitVec (labC $r1).toBitVec (labC $r2).toBitVec lb s) ?_ rfl
    (by decide) hpl s g ⟨hd8, by simpa [twinT] using h11⟩).mono fun _ hx => ⟨hx, trivial⟩
  cfg_cases_env [$ids,*]
  twin_cases))

/-- **The enqueuer's twin, every placement**: from `main_e` with `dmem`
empty and the link at `ra`, every run that stops is at `ra`. -/
theorem pureE_fragX : FragSpecEnv (SharedEnv.counted (EnvRT sAll)) fragE "main_e" PreRF
    (fun _ _ _ _ _ => True) := by
  twin_runF fragE "main_e" "ret_e1" "ret_e2" [fragE, mainETxt, enqFrag, mainEBody, retE1Body, retE2Body]

/-- **The dequeuer's twin, every placement**, from `main_d`. -/
theorem pureD_fragX : FragSpecEnv (SharedEnv.counted (EnvRT sAll)) fragD "main_d" PreRF
    (fun _ _ _ _ _ => True) := by
  twin_runF fragD "main_d" "ret_d1" "ret_d2" [fragD, mainDTxt, deqFrag, mainDBody, retD1Body, retD2Body]

/-! ## The threads and the headline -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqXR)]

/-- The enqueuer's static fields (the x64 MS queue pilot's `enqT` without `pure`, `main`). -/
noncomputable def enqS (P : Params) : LowerStaticX 0 sAll (MQX P) where
  e := layout msqXR
  valid := inferInstance
  pl := planE P
  hpl := planE_valid P
  shape := msqXR_phase1FX
  entry := labX "main_e"
  endPc := labX "done"
  stuck := msqXR_stuck
  Q x := x.1.2 = labX "done" ∧ ComE P x.2.1
  Q_end _ h := h.1
  hB := hB_E P

/-- The dequeuer's static fields. -/
noncomputable def deqS (P : Params) : LowerStaticX 1 sAll (MQX P) where
  e := layout msqXR
  valid := inferInstance
  pl := planD P
  hpl := planD_valid P
  shape := msqXR_phase1FX
  entry := labX "main_d"
  endPc := labX "done"
  stuck := msqXR_stuck
  Q x := x.1.2 = labX "done" ∧ Dn P (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13) x.2.1
  Q_end _ h := h.1
  hB := hB_D P

/-- **The enqueuer from fragment specs**: `pure` from `pureE_fragX`, `main`
from `mainE_fragX`, the return address read as `labX "done"`. -/
noncomputable def enqTF (P : Params) (hL : QLocs P) : LowerThreadX 0 sAll (MQX P) :=
  LowerThreadX.ofFrag
    ((enqS P).ofFragPure pureE_fragX.toL msqXR_placed (by decide) rfl (PreRF (labX "done"))
      (fun x => x.1.2 = labX "done") (fun _ h => h) (fun _ _ h => h) (fun _ _ _ _ _ _ => rfl))
    (mainE_fragX P hL) msqXR_placed (by decide) rfl (MainEPre P (labX "done")) (fun _ _ h => h)
    (fun _ _ _ _ _ h => ⟨rfl, h⟩)

/-- **The dequeuer from fragment specs.** -/
noncomputable def deqTF (P : Params) (hL : QLocs P) (hpt : P.trk = false) : LowerThreadX 1 sAll (MQX P) :=
  LowerThreadX.ofFrag
    ((deqS P).ofFragPure pureD_fragX.toL msqXR_placed (by decide) rfl (PreRF (labX "done"))
      (fun x => x.1.2 = labX "done") (fun _ h => h) (fun _ _ h => h) (fun _ _ _ _ _ _ => rfl))
    (mainD_fragX P hL hpt) msqXR_placed (by decide) rfl (MainDPre P (labX "done")) (fun _ _ h => h)
    (fun _ _ _ _ _ h => ⟨rfl, h⟩)

/-- The two threads. -/
noncomputable def msqTF (P : Params) (hL : QLocs P) (hpt : P.trk = false) :
    (tid : Nat) → tid < 2 → LowerThreadX tid sAll (MQX P)
  | 0, _ => enqTF P hL
  | 1, _ => deqTF P hL hpt
  | _ + 2, h => absurd h (by omega)

/-- **`MsqXR.msqXR_promising` through fragment specs** (same statement): the
threads' `main` and `pure` come from `mainE_fragX`/`mainD_fragX` and
`pureE_fragX`/`pureD_fragX`; no per-text `main`/`pure` proof is used. -/
theorem msqXR_promising_viaFragKitX {fuel : Nat} {P : Params} (hL : QLocs P) (hpt : P.trk = false)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE P s0) (h1 : StartD P s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : MsQueue2FinalX P.n1 P.n2 cfg := by
  refine lower_promising_x64 (Φ := MsQueue2FinalX P.n1 P.n2) fuel sAll_le16 (erase_init hL _) rfl
    (msqTF P hL hpt) ?_ hc hf ?_
  · intro tid h
    rcases tid with _ | _ | i
    · exact ⟨⟨h0.exe, h0.decls, h0.endPc, h0.pc, split_sAll h0.dmem, 0, d8_of_dmem h0.dmem, h0.r11⟩,
        0, h0.r11, h0.rbx, h0.r12, h0.r13, d8_of_dmem h0.dmem, e0_init P _⟩
    · exact ⟨⟨h1.exe, h1.decls, h1.endPc, h1.pc, split_sAll h1.dmem, 0, d8_of_dmem h1.dmem, h1.r11⟩,
        0, h1.r11, h1.rbx, h1.r14, d8_of_dmem h1.dmem, comD_init P _ hi⟩
    · simp only [List.length_cons, List.length_nil] at h; omega
  intro rF' g' E' hle hsize hB
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw P).mono hle
  have fin : ∀ i, i < cfg.threads.size → MQX P cfg (rF' i) g' → 1 ≤ ((rF' i).wr P.tokH).q ∨
      MsQueue2FinalX P.n1 P.n2 cfg := by
    rintro i hi (⟨th, hth, hd, hiv, hacq⟩ | hq)
    · exact .inr ⟨th, hth, final_values E' hW hL hiv
        (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hd⟩
    · exact .inl hq
  rcases fin 0 hi0 (hB 0 (Config.final_done hf hi0)) with hq0 | h
  · rcases fin 1 hi1 (hB 1 (Config.final_done hf hi1)) with hq1 | h
    · exact (tokH_pair_false E' hi0 hi1 (by decide) hq0 hq1).elim
    · exact h
  · exact h

/-- The statement is the original one. -/
example : @msqXR_promising_viaFragKitX = @MsqXR.msqXR_promising := rfl

end Kraken.Promising.Lower.FragKitX

#print axioms Kraken.Promising.Lower.FragKitX.mainE_fragX
#print axioms Kraken.Promising.Lower.FragKitX.mainD_fragX
#print axioms Kraken.Promising.Lower.FragKitX.pureE_fragX
#print axioms Kraken.Promising.Lower.FragKitX.pureD_fragX
#print axioms Kraken.Promising.Lower.FragKitX.msqXR_promising_viaFragKitX
