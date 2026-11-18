import Kraken.X64.Examples.Sbr.SessionBin.Top
import Kraken.X64.Examples.Sbr.SessionBin.MultiSplit

/-!
# The SBR decoder's entry points, one theorem each

One theorem per entry point of FFmpeg's SBR decoder, over the linked machine code, in the
vocabulary of `SessionSpec` §26. Each is proved from the results that make up the conjuncts of
`sbr_session_safe` (`init_safe`, `dec_top`, `usac_top`, `config_top`, `apply_top`): the memory is
regrouped, the element's address facts (`ElemOK`) are moved into the element's predicate, and the
reader's bound is restated as `ReaderOK`.

## The parameters

* `t` is the machine state at the call (registers and data memory `t.dmem`), `s` the state at the
  return, `ra` the return address.
* `S : Setup` fixes the environment: the external routines' stack need `S.k`, their memory
  (transform tables, logging state, …) and FFmpeg's Huffman tables. Init's `InitExt S X` assumes
  the external routines' contracts at `S`; the element carries them afterwards, so the other four
  theorems do not repeat them.
* `X` is the allocator's and the transforms' state. The element's memory comes out of it: the
  model's memory never grows, so the block `av_mallocz` returns was part of `X` before the call.

## The protocol

| Call | Element before | Element after | Other endings |
|---|---|---|---|
| `ff_aac_sbr_ctx_alloc_init` | none | `SbrInitialized` (result 0), or none (`InitFailed`) | none |
| `ff_aac_sbr_decode_extension` | `SbrInitialized` | `SbrReady` | trap |
| `ff_aac_sbr_decode_usac_data` | `SbrInitialized` | `SbrReady` if 0, else `SbrInitialized` | trap |
| `ff_aac_sbr_config_usac` | `SbrInitialized` | `SbrReady` | none |
| `ff_aac_sbr_apply` | `SbrReady` | `SbrReady` | none |

`SbrReady.initialized`: a ready element is initialized, so any call may follow any call whose
"after" meets its "before".

With an element already initialized, init is `ff_aac_sbr_ctx_alloc_init_another_spec`: before,
the other element `SbrInitialized`; after, the new element `SbrInitialized` and the other
element's own part `SbrElemInitialized` (result 0), or the other `SbrInitialized` again
(`InitFailed`). `ff_aac_sbr_ctx_alloc_init_another_ready_spec` is the same with the other
element ready before (`SbrReady`), and still ready after (`SbrElemReady`, or `SbrReady` on
failure). `sbr_switch_element` and its variants (no call) choose which element is
`SbrInitialized`; see "More than one element" below.

## How to read these as memory safety

Each theorem has the form "if memory is the disjoint union of these regions, then every run
returns, with memory the disjoint union of those regions". Three facts of the machine model make
this memory safety (they are read off the model's definitions, not proved as Lean theorems here):

1. **The machine has only the memory listed.** `t.dmem` is the whole data memory of the model;
   the precondition says it is exactly the listed regions, one per line, all disjoint. Code is
   not in data memory: the model keeps the program separately, so self-modifying code is outside
   it, and "address" below means a data address.
2. **An access outside it cannot happen.** A load or store at an address not in `t.dmem` has no
   successor (`nonmem_load`/`nonmem_store` map to `False`), and every write, including `call` and
   `push`, goes through the checked store, so memory never grows.
3. **Every run, every step.** `Returns` (and `ReturnsOrTraps`) is an inductive `Eventually`: every
   step of every run is defined, up to the return to `ra`, and since the definition is
   well-founded every run ends after finitely many steps.

The external routines' instructions are part of every run too; for them the theorems rest on
their assumed contracts (`InitExt`), not on their code.

`Rest` is everything else the caller owns, of any shape. Two choices of it give the plain
statements, proved for `ff_aac_sbr_apply` as corollaries (they follow in the same way for the
other four, by the same choice of `Rest`; those are not stated separately):
* `ff_aac_sbr_apply_only_its_regions`: with nothing else in memory, every run still returns, so
  no instruction reads or writes any other address;
* `ff_aac_sbr_apply_keeps_the_rest`: whatever exact bytes the rest holds, the same bytes are
  there afterwards.

With a non-empty `Rest`, "touches nothing else" follows from the first corollary by locality
(adding memory does not change a run that is defined on less). That step is the standard
separation-logic argument; it is not itself a Lean theorem here.

The two parsers may instead stop at FFmpeg's `abort` (an `av_assert0`) or the bounds trap `ud1`.
Every step up to the stop is a defined one, so a trap is a controlled stop, not an access outside
the listed regions.

## Non-vacuity

The hypotheses are jointly satisfiable (`SessionBin/Witness.lean`, `Wit.wit_session`): under one
ambient code (the laid-out image of every text of `SbrBinary`, with small stand-ins for the
external routines), one `S` and one allocator state `X` (a bump allocator's heap with room for
init's element), every theorem's hypotheses hold of concrete parameters and a concrete machine
state. Each stand-in is proved against its contract, `BandsOK` holds for its `powf`/`log2f`, and
`Wit.wit_init_success` shows that its `av_mallocz` and `av_tx_init` can succeed. This shows the
assumptions consistent; that FFmpeg's real routines meet them is the separate evidence of
translation validation and testing. The element in the witnesses of the four post-init
theorems is in the state init leaves, not obtained by running init.

For init with an element already there (`ff_aac_sbr_ctx_alloc_init_another_spec` and its
`_ready` variant), `SessionBin/WitAnother.lean`, `Wit.wit_init_another`: at the same code, setup
and allocator state, the stack, an initialized (resp. ready) element, `*ac`'s three fields, the
slot `*che_slot` and the allocator's heap, which has room for a second element, are disjoint
regions of one memory, so all hypotheses of both theorems hold. That a second init succeeds is
not shown.

## What is not claimed

* **Functional correctness.** Output buffers, bitstream bytes and the element's contents are owned
  but unspecified.
* **When a trap happens.** The theorems allow a trap; they do not say for which inputs.
* **Teardown.** No entry point gives back the element or the shared data; there is no theorem for
  `ff_aac_sbr_ctx_close`.

## More than one element

An element is initialized for one decoder `ac`. Besides its own allocation, `SbrInitialized`
holds the parts all elements of that decoder share (`SbrShared`): the cell `ac->fdsp`, the
`float_dsp` routine table it points to, and `SharedData`. Only one element at a time holds
them; every other element is represented by its *own part* only: its allocation, without the
shared parts (`SbrElemInitialized`, or `SbrElemReady` if it is ready), which mentions no
decoder. An element is *ready* (`SbrReady`, what `ff_aac_sbr_apply` needs) when no parse has
failed since it was created, configured (`ff_aac_sbr_config_usac`) or last parsed successfully;
in particular it is ready right after init. Switching (no call) hands the shared parts from
one element to another and keeps whether each element is ready: `sbr_switch_element`,
`sbr_switch_element_ready`, `sbr_switch_from_ready`, `sbr_switch_ready`. Which element "holds"
the shared parts is only a way of writing the memory as a list of disjoint regions: nothing
moves in memory and no code runs; the caller just chooses the element it will call next.

The switches speak of the two parts they name. In a longer region list, such as the `h_mem` of a
call ending in `Rest`, they apply to those two lines and leave the other lines as they are: the
order of a region list does not matter, and replacing two disjoint parts by an equivalent pair
keeps the rest (`regions_replace`). The theorems `walk_step3`, …, `walk_next_step5` below check
the switch steps of this walk-through on such a list, with a third element's own part among
the other lines.

FFmpeg creates the elements when it sets up a channel configuration: usually once, before the
first frame, but also while decoding, when a frame's elements do not match the configuration
(`ff_aac_get_che`); then the elements already there may be ready, which
`ff_aac_sbr_ctx_alloc_init_another_ready_spec` covers. In each frame FFmpeg first parses the SBR
data of every element and only then applies SBR to each element. With two elements A and B:

1. `ff_aac_sbr_ctx_alloc_init_spec` creates A: `SbrInitialized S A ac`.
2. `ff_aac_sbr_ctx_alloc_init_another_spec` takes A as `SbrInitialized` and creates B:
   `SbrInitialized S B ac` and A's own part `SbrElemInitialized S A`. If it fails, A is
   `SbrInitialized S A ac` again.

Then, in each frame:

3. `sbr_switch_element`: A is initialized, B is its own part (checked: `walk_step3`).
4. `ff_aac_sbr_decode_extension_spec` on A: A is ready (`SbrReady`).
5. `sbr_switch_from_ready`: B is initialized, A's own part stays ready (`SbrElemReady`)
   (checked: `walk_step5`).
6. `ff_aac_sbr_decode_extension_spec` on B: B is ready.
7. `sbr_switch_ready`: A is ready, B's own part stays ready (checked: `walk_step7`).
8. `ff_aac_sbr_apply_spec` on A: A is still ready.
9. `sbr_switch_ready`: B is ready, A's own part stays ready (checked: `walk_step9`).
10. `ff_aac_sbr_apply_spec` on B.

In the next frame both elements start ready, so steps 3 and 5 are `sbr_switch_ready`, and
`SbrReady.initialized` gives each parse its `SbrInitialized`. Checked: `walk_next_step3`,
`walk_next_step5`.

`sbrInitialized_split` and `sbrReady_split` are the equivalences underneath.

`SbrInitialized` also records that the element's environment shares the caller's tables and
state (`EnvShares`: the transforms' and PS tables, `av_log`'s state and the three `float_dsp`
routines are `S.env`'s). Init establishes it, and the four other entry points take and give back
`SbrInitialized`/`SbrReady` as before, so it changes nothing in their use.

An element's own part may be joined with the shared part of any decoder `ac` of the same `S`:
the statements do not tie it to the `ac` it was created for. This matches FFmpeg: neither
`ChannelElement` (`aacdec.h`) nor `ExtChannelElement` (`aacsbr_template.c`) nor
`SpectralBandReplication` (`sbr.h`) stores a pointer to the decoder context; every entry point
receives `ac` as its first argument and reads `ac->fdsp` at the call.

The limits:
* no witness shows that two elements can be live at once (init may fail; the non-vacuity heap
  fits one element);
* the calls are sequential, on the elements of one decoder (one shared `ac`);
* there is no teardown (see above).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-! ## Regrouping lemmas (private; reassociation and commutation of `⋆` only) -/

section Lemmas

omit [CodeEnv]

private theorem g_sep_l {G G' F : Mem 64 → Prop} (h : ∀ m, G m → G' m) {m : Mem 64}
    (hm : (G ⋆ F) m) : (G' ⋆ F) m := by
  obtain ⟨a, b, hu, hi, ha, hb⟩ := hm
  exact ⟨a, b, hu, hi, h a ha, hb⟩

private theorem g_sep_r {A P Q : Mem 64 → Prop} (h : ∀ m, P m → Q m) {m : Mem 64}
    (hm : (A ⋆ P) m) : (A ⋆ Q) m := by
  obtain ⟨a, b, hu, hi, ha, hb⟩ := hm
  exact ⟨a, b, hu, hi, ha, h b hb⟩

/-- A pure fact inside the third conjunct comes out. -/
private theorem g_pure_out {A B P F : Mem 64 → Prop} {Q : Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ ((fun m => Q ∧ P m) ⋆ F))) m) : Q ∧ (A ⋆ (B ⋆ (P ⋆ F))) m := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, e, f, hu3, hi3, ⟨hq, he⟩, hf⟩ := h
  exact ⟨hq, a, b, hu, hi, ha, c, d, hu2, hi2, hc, e, f, hu3, hi3, he, hf⟩

/-- … and goes back in. -/
private theorem g_pure_in {A B P F : Mem 64 → Prop} {Q : Prop} {m : Mem 64} (hq : Q)
    (h : (A ⋆ (B ⋆ (P ⋆ F))) m) : (A ⋆ (B ⋆ ((fun m => Q ∧ P m) ⋆ F))) m := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, e, f, hu3, hi3, he, hf⟩ := h
  exact ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, e, f, hu3, hi3, ⟨hq, he⟩, hf⟩

/-- The flat list `stack ⋆ E ⋆ A ⋆ (R ⋆ B) ⋆ X ⋆ F` of the two parsers, nested as their
contracts state it. -/
private theorem g_parse {S1 S2 E A R B X F : Mem 64 → Prop} {m : Mem 64} :
    (m =⋆ (S1 ⋆ S2) ⋆ E ⋆ A ⋆ (R ⋆ B) ⋆ X ⋆ F)
      = (m =⋆ S1 ⋆ (S2 ⋆ (E ⋆ (A ⋆ (R ⋆ (B ⋆ (X ⋆ F))))))) := by
  have e : (S1 ⋆ S2) ⋆ E ⋆ A ⋆ (R ⋆ B) ⋆ X ⋆ F
      = S1 ⋆ (S2 ⋆ (E ⋆ (A ⋆ (R ⋆ (B ⋆ (X ⋆ F)))))) := by ac_rfl
  rw [e]

/-- `ff_aac_sbr_config_usac`'s list. -/
private theorem g_cfg {S1 S2 E A F : Mem 64 → Prop} {m : Mem 64} :
    (m =⋆ (S1 ⋆ S2) ⋆ E ⋆ A ⋆ F) = (m =⋆ S1 ⋆ (S2 ⋆ (E ⋆ (A ⋆ F)))) := by
  have e : (S1 ⋆ S2) ⋆ E ⋆ A ⋆ F = S1 ⋆ (S2 ⋆ (E ⋆ (A ⋆ F))) := by ac_rfl
  rw [e]

/-- `ff_aac_sbr_apply`'s list. -/
private theorem g_apply {S1 S2 E A O F : Mem 64 → Prop} {m : Mem 64} :
    (m =⋆ (S1 ⋆ S2) ⋆ E ⋆ A ⋆ O ⋆ F) = (m =⋆ S1 ⋆ (S2 ⋆ (E ⋆ (A ⋆ (O ⋆ F))))) := by
  have e : (S1 ⋆ S2) ⋆ E ⋆ A ⋆ O ⋆ F = S1 ⋆ (S2 ⋆ (E ⋆ (A ⋆ (O ⋆ F)))) := by ac_rfl
  rw [e]

/-- `ff_aac_sbr_ctx_alloc_init`'s list, as `InitPre` nests it. -/
private theorem g_init_pre {Sp Rs Ac Fd Fw Ch Tx Pt Ex Cs Ps X Fr : Mem 64 → Prop}
    {m : Mem 64}
    (h : m =⋆ (Sp ⋆ Rs) ⋆ (Ac ⋆ (Fd ⋆ Fw)) ⋆ Ch ⋆ (Tx ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ Ps)))) ⋆ X ⋆ Fr) :
    m =⋆ Sp ⋆ (Rs ⋆ ((Ch ⋆ (Tx ⋆ X)) ⋆ (Ac ⋆ (Fd ⋆ (Fw ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ (Ps ⋆ Fr)))))))))
    := by
  have e : (Sp ⋆ Rs) ⋆ (Ac ⋆ (Fd ⋆ Fw)) ⋆ Ch ⋆ (Tx ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ Ps)))) ⋆ X ⋆ Fr
      = Sp ⋆ (Rs ⋆ ((Ch ⋆ (Tx ⋆ X)) ⋆ (Ac ⋆ (Fd ⋆ (Fw ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ (Ps ⋆ Fr)))))))))
    := by ac_rfl
  rw [← e]; exact h

/-- Init's success memory, flat. -/
private theorem g_init_ok {Sp Rs E A C X Fr : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ Sp ⋆ (Rs ⋆ (E ⋆ (A ⋆ (C ⋆ (X ⋆ Fr)))))) :
    m =⋆ (Sp ⋆ Rs) ⋆ E ⋆ A ⋆ C ⋆ X ⋆ Fr := by
  have e : (Sp ⋆ Rs) ⋆ E ⋆ A ⋆ C ⋆ X ⋆ Fr = Sp ⋆ (Rs ⋆ (E ⋆ (A ⋆ (C ⋆ (X ⋆ Fr))))) := by
    ac_rfl
  rw [e]; exact h

/-- Init's failure memory, flat, with what is left at `che_slot` weakened to `G'`. -/
private theorem g_init_fail {Sp Rs G G' Tx X Ac Fd Fw Pt Ex Cs Ps Fr : Mem 64 → Prop}
    {m : Mem 64} (hG : ∀ m, G m → G' m)
    (h : m =⋆ Sp ⋆ (Rs ⋆ ((G ⋆ (Tx ⋆ X)) ⋆ (Ac ⋆ (Fd ⋆ (Fw ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ (Ps
      ⋆ Fr)))))))))) :
    m =⋆ (Sp ⋆ Rs) ⋆ G' ⋆ (Ac ⋆ (Fd ⋆ Fw)) ⋆ (Tx ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ Ps)))) ⋆ X ⋆ Fr := by
  have e : Sp ⋆ (Rs ⋆ ((G ⋆ (Tx ⋆ X)) ⋆ (Ac ⋆ (Fd ⋆ (Fw ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ (Ps
      ⋆ Fr)))))))))
      = G ⋆ ((Sp ⋆ Rs) ⋆ (Ac ⋆ (Fd ⋆ Fw)) ⋆ (Tx ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ Ps)))) ⋆ X ⋆ Fr) := by
    ac_rfl
  have e' : G' ⋆ ((Sp ⋆ Rs) ⋆ (Ac ⋆ (Fd ⋆ Fw)) ⋆ (Tx ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ Ps)))) ⋆ X ⋆ Fr)
      = (Sp ⋆ Rs) ⋆ G' ⋆ (Ac ⋆ (Fd ⋆ Fw)) ⋆ (Tx ⋆ (Pt ⋆ (Ex ⋆ (Cs ⋆ Ps)))) ⋆ X ⋆ Fr := by
    ac_rfl
  rw [e] at h
  rw [← e']
  exact g_sep_l hG h

private theorem g_assoc2 {C E T : Mem 64 → Prop} : C ⋆ (E ⋆ T) = (C ⋆ E) ⋆ T := by ac_rfl

private theorem g_assoc3 {C E K T : Mem 64 → Prop} :
    C ⋆ (E ⋆ (K ⋆ T)) = (C ⋆ (E ⋆ K)) ⋆ T := by ac_rfl

end Lemmas

/-- A ready element is initialized: after init, a successful parse or `ff_aac_sbr_config_usac`,
the element may be parsed again. -/
theorem SbrReady.initialized {S : Setup} {che ac : BitVec 64} {m : Mem 64}
    (h : SbrReady S che ac m) : SbrInitialized S che ac m :=
  ⟨h.1, true, h.2⟩

/-! ## The five entry points -/

/-- **`ff_aac_sbr_ctx_alloc_init(ac, che_slot, id_aac)`**: create the SBR element.

*Before the call.* `rdi = ac`; `rsi = che_slot`, the address of the `ChannelElement` pointer to
set; the low 32 bits of `rdx` are `id_aac`; `rsp = sp`. Memory is the disjoint union of the
regions listed in `h_mem`, one per line.

*Assumed.* The machine code is the linked binary's (`SbrBinary`; evidence: translation
validation). The external routines (`av_mallocz`, `av_tx_init`, the DSP initializers, and those
the element calls later) meet their contracts at `S.env` with state `X` (`InitExt`); in
particular `av_mallocz` returns a 32-aligned block in the lower half of the address space.
No stack alignment and no `StackBound` are needed.

*After, in every run.* The procedure returns to `ra` with the ABI's registers (`AbiReturn`), and
either
* the result is `0`: for some `p`, `*che_slot = p` and the element at `p` is initialized; the
  shared data, `ac->fdsp` and its routine table now belong to the element; or
* the result is negative: no element exists; the caller has its regions back, and at `che_slot`
  what the failed allocation left (`InitFailed`). -/
theorem ff_aac_sbr_ctx_alloc_init_spec {S : Setup} {X : Mem 64 → Prop}
    (h_bin : SbrBinary) (h_ext : InitExt S X)
    (ac che_slot : BitVec 64) (id_aac : BitVec 32) (avctx fdsp : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che_slot)
    (h_id : (t.regs.get64 .rdx).setWidth 32 = id_aac) (h_sp : t.regs.get64 .rsp = sp)
    (h_mem : t.dmem =⋆
        StackAt ra sp (initStack S.k)          -- return address; free stack below
      ⋆ AcInit S ac avctx fdsp er ps           -- *ac as the AAC decoder set it up
      ⋆ 8 ?@ che_slot                          -- the slot for the new pointer
      ⋆ SharedData S                           -- tables and state shared with the element
      ⋆ X                                      -- the allocator's and transforms' state
      ⋆ Rest) :                                -- everything else the caller owns
    Returns "ff_aac_sbr_ctx_alloc_init" t ra (fun s => AbiReturn t s ∧
      ((ret32 s = 0#32 ∧ ∃ p : BitVec 64, s.dmem =⋆
            StackAfter sp (initStack S.k)      -- the stack region, back
          ⋆ SbrInitialized S p ac              -- the new element
          ⋆ AcFields ac avctx er ps            -- *ac's three fields
          ⋆ PtrAt che_slot p                   -- *che_slot = p
          ⋆ X
          ⋆ Rest)                              -- holds again (see `..._keeps_the_rest`)
      ∨ ((ret32 s).toInt < 0 ∧ s.dmem =⋆
            StackAfter sp (initStack S.k)
          ⋆ InitFailed S che_slot id_aac       -- what the failed call left
          ⋆ AcInit S ac avctx fdsp er ps
          ⋆ SharedData S
          ⋆ X
          ⋆ Rest))) := by
  subst h_ac h_che h_id h_sp
  have hpre : InitPre S.k S.env.TxTab X (InitOwn S (arg0 t) avctx fdsp er ps Rest) ra t :=
    g_init_pre h_mem
  refine eventually_weaken _ _ _ _ (fun st hs => ?_) (init_safe h_bin.init h_ext hpre)
  rcases hs with ⟨hra, hq⟩ | hf
  · refine Or.inl ⟨hra, ?_⟩
    rcases hq with ⟨h0, p, hE, h1, h2, h3, hm⟩ | ⟨h0, h1, h2, h3, hm⟩
      | ⟨h0, p, bc, bf, hbc, hbf, h1, h2, h3, hm⟩
      | ⟨h0, p, c, f, bc, bf, hbc, hbf, h1, h2, h3, hm⟩
    · exact ⟨⟨h1, h2, h3⟩, Or.inl ⟨h0, p, g_init_ok (g_pure_in hE hm)⟩⟩
    · refine ⟨⟨h1, h2, h3⟩, Or.inr ⟨by rw [h0]; decide, ?_⟩⟩
      exact g_init_fail (fun _ hg => Or.inl hg) hm
    · refine ⟨⟨h1, h2, h3⟩, Or.inr ⟨h0, ?_⟩⟩
      rw [g_assoc2 (C := Apply.c8 _ p)] at hm
      exact g_init_fail (fun _ hg => Or.inr (Or.inl ⟨p, bc, bf, hbc, hbf, hg⟩)) hm
    · refine ⟨⟨h1, h2, h3⟩, Or.inr ⟨h0, ?_⟩⟩
      rw [g_assoc3 (C := Apply.c8 _ p)] at hm
      exact g_init_fail (fun _ hg => Or.inr (Or.inr ⟨p, c, f, bc, bf, hbc, hbf, hg⟩)) hm
  · exact Or.inr hf

/-- **`ff_aac_sbr_decode_extension(ac, che, gb, crc, cnt, id_aac)`**: parse one SBR extension
payload.

*Before the call.* `rdi = ac`; `rsi = che`, the element; `rdx = gb`; the low 32 bits of `r8` are
`cnt`; `crc` and `id_aac` are unconstrained; `rsp = sp`, 16-aligned at the call. The reader is
in bounds (`ReaderOK i p8 L`). Memory is the disjoint union of the regions in `h_mem`.

*Assumed.* `SbrBinary` and `StackBound S`. The external routines' contracts came with the
element (`SbrInitialized`, from init's `InitExt`).

*After, in every run.* Either the procedure returns to `ra` with `AbiReturn` and the result
`cnt`, the element ready, the reader's index advanced to some `i'` still in bounds,
`ext_sample_rate` possibly changed to some `er'`, and the other regions back; or the run stops at
FFmpeg's `abort` or the bounds trap `ud1` (`ReturnsOrTraps`). -/
theorem ff_aac_sbr_decode_extension_spec {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che gb : BitVec 64) (cnt : BitVec 32) (avctx : BitVec 64) (er ps : BitVec 32)
    (buf : BitVec 64) (i sib p8 pad : BitVec 32) (L : Nat)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_gb : t.regs.get64 .rdx = gb) (h_cnt : (t.regs.get64 .r8).setWidth 32 = cnt)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp) (h_rd : ReaderOK i p8 L)
    (h_mem : t.dmem =⋆
        StackAt ra sp (decStack S.k)           -- return address; free stack below
      ⋆ SbrInitialized S che ac                -- the element
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ DecReader gb buf i sib p8 pad L        -- *gb and its buffer
      ⋆ DecScratch ac avctx                    -- fields decode may overwrite
      ⋆ Rest) :                                -- everything else the caller owns
    ReturnsOrTraps "ff_aac_sbr_decode_extension" t ra (fun s => AbiReturn t s
      ∧ ret32 s = cnt ∧ ∃ (i' er' : BitVec 32), ReaderOK i' p8 L ∧ s.dmem =⋆
          StackAfter sp (decStack S.k)         -- the stack region, back
        ⋆ SbrReady S che ac                    -- the element, now ready
        ⋆ AcFields ac avctx er' ps             -- ext_sample_rate may change
        ⋆ DecReader gb buf i' sib p8 pad L     -- index advanced, in bounds; bytes unspecified
        ⋆ DecScratch ac avctx                  -- contents unspecified
        ⋆ Rest) := by                          -- holds again (see `..._keeps_the_rest`)
  subst h_ac h_che h_gb h_cnt h_sp
  rw [g_parse] at h_mem
  obtain ⟨hE, hm⟩ := g_pure_out h_mem
  have hc : DecCall (arg1 t) (arg0 t) ⟨⟨buf, p8, L⟩, sib, pad⟩ i t :=
    ⟨⟨rfl, rfl⟩, hE, h_rd, h_align⟩
  refine eventually_weaken _ _ _ _ (fun st hs => ?_) (dec_top h_bin S h_stk hc hm)
  rcases hs with ⟨hra, i', er', hi', hr, h1, h2, h3, hm'⟩ | hf
  · refine Or.inl ⟨hra, ⟨h1, h2, h3⟩, hr, i', er', ⟨hi', h_rd.2⟩, ?_⟩
    rw [g_parse]; exact g_pure_in hE hm'
  · exact Or.inr hf

/-- **`ff_aac_sbr_decode_usac_data(ac, che, ue, gb, …)`**: parse one USAC SBR payload.

*Before the call.* `rdi = ac`; `rsi = che`, the element; `rdx = ue`; `rcx = gb`; the further
arguments are unconstrained; `rsp = sp`, 16-aligned at the call. The reader is in bounds
(`ReaderOK`), and `ue->sbr`'s twelve bytes `uev` are in range (`UsacSbrOK`). Memory is the
disjoint union of the regions in `h_mem`.

*Assumed.* `SbrBinary` and `StackBound S`.

*After, in every run.* Either the procedure returns to `ra` with `AbiReturn`, the reader's index
advanced to some `i'` still in bounds, the other regions back, and the element ready if the
result is `0`, otherwise still initialized; or the run stops at a trap (`ReturnsOrTraps`). -/
theorem ff_aac_sbr_decode_usac_data_spec {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che ue gb : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (buf : BitVec 64) (i p8 : BitVec 32) (L : Nat) (uev : List UInt8)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_ue : t.regs.get64 .rdx = ue) (h_gb : t.regs.get64 .rcx = gb)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp)
    (h_rd : ReaderOK i p8 L) (h_uev : UsacSbrOK uev)
    (h_mem : t.dmem =⋆
        StackAt ra sp (usacStack S.k)          -- return address; free stack below
      ⋆ SbrInitialized S che ac                -- the element
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ UsacReader gb buf i p8 L               -- *gb and its buffer
      ⋆ uev =@ (ue + 0xc#64)                   -- ue->sbr, twelve bytes
      ⋆ Rest) :                                -- everything else the caller owns
    ReturnsOrTraps "ff_aac_sbr_decode_usac_data" t ra (fun s => AbiReturn t s
      ∧ ∃ i' : BitVec 32, ReaderOK i' p8 L ∧
        ((ret32 s = 0#32 ∧ s.dmem =⋆
            StackAfter sp (usacStack S.k)
          ⋆ SbrReady S che ac                  -- result 0: the element is ready
          ⋆ AcFields ac avctx er ps
          ⋆ UsacReader gb buf i' p8 L          -- index advanced, in bounds
          ⋆ uev =@ (ue + 0xc#64)
          ⋆ Rest)
        ∨ (ret32 s ≠ 0#32 ∧ s.dmem =⋆
            StackAfter sp (usacStack S.k)
          ⋆ SbrInitialized S che ac            -- otherwise: still initialized
          ⋆ AcFields ac avctx er ps
          ⋆ UsacReader gb buf i' p8 L
          ⋆ uev =@ (ue + 0xc#64)
          ⋆ Rest))) := by
  subst h_ac h_che h_ue h_gb h_sp
  rw [g_parse] at h_mem
  obtain ⟨hE, hm⟩ := g_pure_out h_mem
  let u : UsacIn := ⟨arg2 t, arg3 t, buf, p8, L, uev⟩
  have hc : UsacCall (arg1 t) (arg0 t) u i t :=
    ⟨⟨rfl, rfl, rfl, rfl⟩, hE, h_rd,
      ⟨h_uev.1, h_uev.2.1, h_uev.2.2.2.1, h_uev.2.2.2.2⟩, h_uev.2.2.1, h_align⟩
  refine eventually_weaken _ _ _ _ (fun st hs => ?_) (usac_top h_bin S h_stk hc hm)
  rcases hs with ⟨hra, i', hi', h1, h2, h3, hm'⟩ | hf
  · refine Or.inl ⟨hra, ⟨h1, h2, h3⟩, i', ⟨hi', h_rd.2⟩, ?_⟩
    by_cases h0 : ret32 st.1 = 0#32
    · simp only [h0, decide_true] at hm'
      refine Or.inl ⟨h0, ?_⟩
      rw [g_parse]; exact g_pure_in hE hm'
    · simp only [h0, decide_false] at hm'
      refine Or.inr ⟨h0, ?_⟩
      rw [g_parse]
      refine g_pure_in hE ?_
      exact g_sep_r (fun _ h1 => g_sep_r (fun _ h2 => g_sep_l (fun _ hg => ⟨false, hg⟩) h2) h1) hm'
  · exact Or.inr hf

/-- **`ff_aac_sbr_config_usac(ac, che, ue)`**: configure the element for USAC.

*Before the call.* `rdi = ac`; `rsi = che`, the element; `ue` is unconstrained; `rsp = sp`.
Memory is the disjoint union of the regions in `h_mem`; no stack below the return address is
used.

*Assumed.* `SbrBinary` only: the procedure calls nothing, so it needs neither stack alignment nor
`StackBound`.

*After, in every run.* The procedure returns to `ra` with `AbiReturn`, the result `0`, the
element ready (SBR switched off until the next parse), and the other regions back. -/
theorem ff_aac_sbr_config_usac_spec {S : Setup} (h_bin : SbrBinary)
    (ac che : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_sp : t.regs.get64 .rsp = sp)
    (h_mem : t.dmem =⋆
        StackAt ra sp 0                        -- return address only
      ⋆ SbrInitialized S che ac                -- the element
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ Rest) :                                -- everything else the caller owns
    Returns "ff_aac_sbr_config_usac" t ra (fun s => AbiReturn t s ∧ ret32 s = 0#32 ∧ s.dmem =⋆
        StackAfter sp 0
      ⋆ SbrReady S che ac                      -- the element, now ready
      ⋆ AcFields ac avctx er ps
      ⋆ Rest) := by                            -- holds again (see `..._keeps_the_rest`)
  subst h_ac h_che h_sp
  rw [g_cfg] at h_mem
  obtain ⟨hE, hm⟩ := g_pure_out h_mem
  refine eventually_weaken _ _ _ _ (fun st hs => ?_) (config_top h_bin S ⟨⟨rfl, rfl⟩⟩ hm)
  rcases hs with ⟨hra, hr, h1, h2, h3, hm'⟩ | hf
  · refine Or.inl ⟨hra, ⟨h1, h2, h3⟩, hr, ?_⟩
    rw [g_cfg]; exact g_pure_in hE hm'
  · exact Or.inr hf

/-- **`ff_aac_sbr_apply(ac, che, id_aac, L, R)`**: run the SBR synthesis for one frame.

*Before the call.* `rdi = ac`; `rsi = che`, the element; `rcx = L` and `r8 = R`, the output
buffers, 32-aligned; `id_aac` is unconstrained; `rsp = sp`, 16-aligned at the call. Memory is
the disjoint union of the regions in `h_mem`.

*Assumed.* `SbrBinary` and `StackBound S`.

*After, in every run.* The procedure returns to `ra` with `AbiReturn`, the element still ready,
the output buffers back (contents unspecified), and the other regions back. -/
theorem ff_aac_sbr_apply_spec {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_L : t.regs.get64 .rcx = L) (h_R : t.regs.get64 .r8 = R)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp)
    (h_out : isAligned 32 L = true ∧ isAligned 32 R = true)
    (h_mem : t.dmem =⋆
        StackAt ra sp (applyStack S.k)         -- return address; free stack below
      ⋆ SbrReady S che ac                      -- the element, ready
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ OutBuffers L R                         -- the output buffers
      ⋆ Rest) :                                -- everything else the caller owns
    Returns "ff_aac_sbr_apply" t ra (fun s => AbiReturn t s ∧ s.dmem =⋆
        StackAfter sp (applyStack S.k)
      ⋆ SbrReady S che ac                      -- still ready
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R                         -- written, contents unspecified
      ⋆ Rest) := by                            -- holds again (see `..._keeps_the_rest`)
  subst h_ac h_che h_L h_R h_sp
  rw [g_apply] at h_mem
  obtain ⟨hE, hm⟩ := g_pure_out h_mem
  have hc : ApplyCall (arg1 t) (arg0 t) t := ⟨⟨rfl, rfl⟩, hE, h_out, h_align⟩
  refine eventually_weaken _ _ _ _ (fun st hs => ?_) (apply_top h_bin S h_stk hc hm)
  rcases hs with ⟨hra, h1, h2, h3, hm'⟩ | hf
  · refine Or.inl ⟨hra, ⟨h1, h2, h3⟩, ?_⟩
    rw [g_apply]; exact g_pure_in hE hm'
  · exact Or.inr hf

/-! ## More than one element

An initialized element (`SbrInitialized`) is two parts: the part all elements of one decoder
share (`SbrShared`: the cell `ac->fdsp`, its `float_dsp` routine table and `SharedData`), and the
element's own part (`SbrElemInitialized`, or `SbrElemReady` after a successful parse). Only one
element at a time holds the shared part. -/

section Multi

omit [CodeEnv]

private theorem g_swap (H A B : Mem 64 → Prop) : H ⋆ A ⋆ B = H ⋆ B ⋆ A := by ac_rfl

private theorem g_front (St H E Af Sl X R : Mem 64 → Prop) :
    St ⋆ (H ⋆ E) ⋆ Af ⋆ Sl ⋆ X ⋆ R = H ⋆ (St ⋆ E ⋆ Af ⋆ Sl ⋆ X ⋆ R) := by ac_rfl

private theorem g_another_pre (C Fd Sd St E Af Sl X R : Mem 64 → Prop) :
    (C ⋆ (Fd ⋆ Sd)) ⋆ (St ⋆ E ⋆ Af ⋆ Sl ⋆ X ⋆ R)
      = St ⋆ (Af ⋆ (C ⋆ Fd)) ⋆ Sl ⋆ Sd ⋆ X ⋆ (E ⋆ R) := by ac_rfl

private theorem g_another_ok (Sa I Af Pt X E R : Mem 64 → Prop) :
    Sa ⋆ I ⋆ Af ⋆ Pt ⋆ X ⋆ (E ⋆ R) = Sa ⋆ I ⋆ E ⋆ Af ⋆ Pt ⋆ X ⋆ R := by ac_rfl

private theorem g_another_fail (Sa F Af C Fd Sd X E R : Mem 64 → Prop) :
    Sa ⋆ F ⋆ (Af ⋆ (C ⋆ Fd)) ⋆ Sd ⋆ X ⋆ (E ⋆ R)
      = ((C ⋆ (Fd ⋆ Sd)) ⋆ E) ⋆ (Sa ⋆ Af ⋆ F ⋆ X ⋆ R) := by ac_rfl

private theorem g_another_back (I Sa Af F X R : Mem 64 → Prop) :
    I ⋆ (Sa ⋆ Af ⋆ F ⋆ X ⋆ R) = Sa ⋆ I ⋆ Af ⋆ F ⋆ X ⋆ R := by ac_rfl

end Multi

/-- **An initialized element is the shared part plus its own part**, and back. The own part
does not depend on the value of `ac->fdsp`, so it can be joined with the shared part whatever
that cell holds. -/
theorem sbrInitialized_split {S : Setup} {che ac : BitVec 64} {m : Mem 64} :
    (m =⋆ SbrInitialized S che ac) ↔ (m =⋆ SbrShared S ac ⋆ SbrElemInitialized S che) := by
  constructor
  · rintro ⟨hE, ok, e, i, σ, he, hsh, hσ, hm⟩
    rw [elemAt_split hsh, Std.ExtHashMap.sep_comm] at hm
    obtain ⟨a, b, hu, hi, ha, hb⟩ := hm
    exact ⟨a, b, hu, hi, ⟨σ.1.fdsp, ha⟩, ⟨ok, hE, e, i, σ, he, hsh, hσ, hb⟩⟩
  · rintro ⟨a, b, hu, hi, ⟨f, ha⟩, ⟨ok, hE, e, i, σ, he, hsh, hσ, hb⟩⟩
    have hσ' : SReach (σInit { i with fdsp := f }) (setF f σ) ok := by
      rw [σInit_setF]; exact sreach_setF f hσ
    refine ⟨hE, ok, e, _, setF f σ, he, hsh, hσ', ?_⟩
    rw [elemAt_split hsh, Std.ExtHashMap.sep_comm, elemOwn_setF]
    exact ⟨a, b, hu, hi, ha, hb⟩

/-- **A ready element is the shared part plus its own part, ready**, and back. -/
theorem sbrReady_split {S : Setup} {che ac : BitVec 64} {m : Mem 64} :
    (m =⋆ SbrReady S che ac) ↔ (m =⋆ SbrShared S ac ⋆ SbrElemReady S che) := by
  constructor
  · rintro ⟨hE, e, i, σ, he, hsh, hσ, hm⟩
    rw [elemAt_split hsh, Std.ExtHashMap.sep_comm] at hm
    obtain ⟨a, b, hu, hi, ha, hb⟩ := hm
    exact ⟨a, b, hu, hi, ⟨σ.1.fdsp, ha⟩, ⟨hE, e, i, σ, he, hsh, hσ, hb⟩⟩
  · rintro ⟨a, b, hu, hi, ⟨f, ha⟩, ⟨hE, e, i, σ, he, hsh, hσ, hb⟩⟩
    have hσ' : SReach (σInit { i with fdsp := f }) (setF f σ) true := by
      rw [σInit_setF]; exact sreach_setF f hσ
    refine ⟨hE, e, _, setF f σ, he, hsh, hσ', ?_⟩
    rw [elemAt_split hsh, Std.ExtHashMap.sep_comm, elemOwn_setF]
    exact ⟨a, b, hu, hi, ha, hb⟩

theorem sbrInitialized_eq (S : Setup) (che ac : BitVec 64) :
    SbrInitialized S che ac = (SbrShared S ac ⋆ SbrElemInitialized S che) :=
  funext fun _ => propext sbrInitialized_split

theorem sbrReady_eq (S : Setup) (che ac : BitVec 64) :
    SbrReady S che ac = (SbrShared S ac ⋆ SbrElemReady S che) :=
  funext fun _ => propext sbrReady_split

/-- **Switching elements.** Of the elements `a` and `b` of one decoder `ac`, the one that holds
the shared part is the initialized one (`SbrInitialized`); the other is only its own part
(`SbrElemInitialized`). The shared part can be handed from `a` to `b` and back, with no call:
before an entry point is called on `b`, switch so that `b` is the initialized one. -/
theorem sbr_switch_element {S : Setup} {a b ac : BitVec 64} {m : Mem 64} :
    (m =⋆ SbrInitialized S a ac ⋆ SbrElemInitialized S b)
      ↔ (m =⋆ SbrInitialized S b ac ⋆ SbrElemInitialized S a) := by
  rw [sbrInitialized_eq S a ac, sbrInitialized_eq S b ac, g_swap]

/-- **Switching to a ready element.** As `sbr_switch_element`, when `b`'s own part is ready
(`SbrElemReady`: no parse on `b` has failed since it was created, configured or last parsed
successfully): after the switch `b` is ready
(`SbrReady`), as `ff_aac_sbr_apply` requires; `a` keeps its own part. -/
theorem sbr_switch_element_ready {S : Setup} {a b ac : BitVec 64} {m : Mem 64} :
    (m =⋆ SbrInitialized S a ac ⋆ SbrElemReady S b)
      ↔ (m =⋆ SbrReady S b ac ⋆ SbrElemInitialized S a) := by
  rw [sbrInitialized_eq S a ac, sbrReady_eq S b ac, g_swap]

/-- **Switching between two ready elements.** As `sbr_switch_element`, keeping both elements
ready: `a` is ready (`SbrReady`) and `b`'s own part is ready (`SbrElemReady`); after the switch
`b` is ready and `a`'s own part stays ready. -/
theorem sbr_switch_ready {S : Setup} {a b ac : BitVec 64} {m : Mem 64} :
    (m =⋆ SbrReady S a ac ⋆ SbrElemReady S b) ↔ (m =⋆ SbrReady S b ac ⋆ SbrElemReady S a) := by
  rw [sbrReady_eq S a ac, sbrReady_eq S b ac, g_swap]

/-- **Switching away from a ready element.** As `sbr_switch_element`, when `a` is ready
(`SbrReady`) and `b` is only initialized: after the switch `b` is initialized and `a`'s own part
stays ready (`SbrElemReady`), so that `ff_aac_sbr_apply` may later run on `a` without a new
parse.

Which switch to use: from a ready element, `sbr_switch_from_ready` (to an initialized one) or
`sbr_switch_ready` (to a ready one); from an initialized element, `sbr_switch_element` (to an
initialized one) or `sbr_switch_element_ready` (to a ready one). -/
theorem sbr_switch_from_ready {S : Setup} {a b ac : BitVec 64} {m : Mem 64} :
    (m =⋆ SbrReady S a ac ⋆ SbrElemInitialized S b)
      ↔ (m =⋆ SbrInitialized S b ac ⋆ SbrElemReady S a) := by
  rw [sbrReady_eq S a ac, sbrInitialized_eq S b ac, g_swap]

omit [CodeEnv] in
/-- **Replacing two regions by an equivalent pair keeps the rest of the list.** If `P` and `Q`
describe the same memories, a region list `P ⋆ R` holds exactly when `Q ⋆ R` does. -/
theorem regions_replace {P Q : Mem 64 → Prop} (h : ∀ m, P m ↔ Q m) (R : Mem 64 → Prop)
    {m : Mem 64} : (m =⋆ P ⋆ R) ↔ (m =⋆ Q ⋆ R) := by
  rw [show P = Q from funext fun m => propext (h m)]

/-! ### The walk-through, checked

The switch steps of the walk-through in the module doc ("More than one element"), on a region
list with a third element `c`'s own part and the rest `Rest`: the switch changes the two lines it
names and keeps the others. -/

/-- Step 3: hand the shared part from `b` (just created) to `a`. -/
theorem walk_step3 {S : Setup} {a b c ac : BitVec 64} {Rest : Mem 64 → Prop} {m : Mem 64} :
    (m =⋆ SbrInitialized S b ac ⋆ SbrElemInitialized S a ⋆ SbrElemInitialized S c ⋆ Rest)
      ↔ (m =⋆ SbrInitialized S a ac ⋆ SbrElemInitialized S b ⋆ SbrElemInitialized S c ⋆ Rest) := by
  rw [Std.ExtHashMap.sep_assoc _ (SbrElemInitialized S c),
    Std.ExtHashMap.sep_assoc _ (SbrElemInitialized S c)]
  exact regions_replace (fun _ => sbr_switch_element) _

/-- Step 5: from `a`, now ready, to `b`; `a`'s own part stays ready. -/
theorem walk_step5 {S : Setup} {a b c ac : BitVec 64} {Rest : Mem 64 → Prop} {m : Mem 64} :
    (m =⋆ SbrReady S a ac ⋆ SbrElemInitialized S b ⋆ SbrElemInitialized S c ⋆ Rest)
      ↔ (m =⋆ SbrInitialized S b ac ⋆ SbrElemReady S a ⋆ SbrElemInitialized S c ⋆ Rest) := by
  rw [Std.ExtHashMap.sep_assoc _ (SbrElemInitialized S c),
    Std.ExtHashMap.sep_assoc _ (SbrElemInitialized S c)]
  exact regions_replace (fun _ => sbr_switch_from_ready) _

/-- Step 7: from `b`, now ready, back to `a`, both ready. -/
theorem walk_step7 {S : Setup} {a b c ac : BitVec 64} {Rest : Mem 64 → Prop} {m : Mem 64} :
    (m =⋆ SbrReady S b ac ⋆ SbrElemReady S a ⋆ SbrElemInitialized S c ⋆ Rest)
      ↔ (m =⋆ SbrReady S a ac ⋆ SbrElemReady S b ⋆ SbrElemInitialized S c ⋆ Rest) := by
  rw [Std.ExtHashMap.sep_assoc _ (SbrElemInitialized S c),
    Std.ExtHashMap.sep_assoc _ (SbrElemInitialized S c)]
  exact regions_replace (fun _ => sbr_switch_ready) _

/-- Step 9: from `a` to `b`, both ready. -/
theorem walk_step9 {S : Setup} {a b c ac : BitVec 64} {Rest : Mem 64 → Prop} {m : Mem 64} :
    (m =⋆ SbrReady S a ac ⋆ SbrElemReady S b ⋆ SbrElemInitialized S c ⋆ Rest)
      ↔ (m =⋆ SbrReady S b ac ⋆ SbrElemReady S a ⋆ SbrElemInitialized S c ⋆ Rest) := by
  rw [Std.ExtHashMap.sep_assoc _ (SbrElemInitialized S c),
    Std.ExtHashMap.sep_assoc _ (SbrElemInitialized S c)]
  exact regions_replace (fun _ => sbr_switch_ready) _

/-- The next frame, step 3: from `b` back to `a`, both ready (here `c` is ready too). -/
theorem walk_next_step3 {S : Setup} {a b c ac : BitVec 64} {Rest : Mem 64 → Prop}
    {m : Mem 64} :
    (m =⋆ SbrReady S b ac ⋆ SbrElemReady S a ⋆ SbrElemReady S c ⋆ Rest)
      ↔ (m =⋆ SbrReady S a ac ⋆ SbrElemReady S b ⋆ SbrElemReady S c ⋆ Rest) := by
  rw [Std.ExtHashMap.sep_assoc _ (SbrElemReady S c),
    Std.ExtHashMap.sep_assoc _ (SbrElemReady S c)]
  exact regions_replace (fun _ => sbr_switch_ready) _

/-- The next frame, step 5: from `a` to `b`, both ready. -/
theorem walk_next_step5 {S : Setup} {a b c ac : BitVec 64} {Rest : Mem 64 → Prop}
    {m : Mem 64} :
    (m =⋆ SbrReady S a ac ⋆ SbrElemReady S b ⋆ SbrElemReady S c ⋆ Rest)
      ↔ (m =⋆ SbrReady S b ac ⋆ SbrElemReady S a ⋆ SbrElemReady S c ⋆ Rest) := by
  rw [Std.ExtHashMap.sep_assoc _ (SbrElemReady S c),
    Std.ExtHashMap.sep_assoc _ (SbrElemReady S c)]
  exact regions_replace (fun _ => sbr_switch_ready) _

/-- Init with an element already there, for any element predicate `W` that is the shared part
and an own part `Wo` (`SbrInitialized`/`SbrElemInitialized` or `SbrReady`/`SbrElemReady`). -/
private theorem init_another {S : Setup} {X : Mem 64 → Prop} {W Wo : Mem 64 → Prop}
    {ac : BitVec 64} (hW : W = (SbrShared S ac ⋆ Wo))
    (h_bin : SbrBinary) (h_ext : InitExt S X)
    (che_slot : BitVec 64) (id_aac : BitVec 32) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che_slot)
    (h_id : (t.regs.get64 .rdx).setWidth 32 = id_aac) (h_sp : t.regs.get64 .rsp = sp)
    (h_mem : t.dmem =⋆
        StackAt ra sp (initStack S.k)          -- return address; free stack below
      ⋆ W                                      -- the element already there
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ 8 ?@ che_slot                          -- the slot for the new pointer
      ⋆ X                                      -- the allocator's and transforms' state
      ⋆ Rest) :                                -- everything else the caller owns
    Returns "ff_aac_sbr_ctx_alloc_init" t ra (fun s => AbiReturn t s ∧
      ((ret32 s = 0#32 ∧ ∃ p : BitVec 64, s.dmem =⋆
            StackAfter sp (initStack S.k)      -- the stack region, back
          ⋆ SbrInitialized S p ac              -- the new element
          ⋆ Wo                                 -- its own part
          ⋆ AcFields ac avctx er ps            -- *ac's three fields
          ⋆ PtrAt che_slot p                   -- *che_slot = p
          ⋆ X
          ⋆ Rest)                              -- holds again
      ∨ ((ret32 s).toInt < 0 ∧ s.dmem =⋆
            StackAfter sp (initStack S.k)
          ⋆ W                                  -- the element, as before
          ⋆ AcFields ac avctx er ps
          ⋆ InitFailed S che_slot id_aac       -- what the failed call left
          ⋆ X
          ⋆ Rest))) := by
  rw [hW] at h_mem
  obtain ⟨a, b, hu, hi, ⟨f, ha⟩, hb⟩ := (congrFun (g_front _ _ _ _ _ _ _) _).mp h_mem
  have hpre := (congrFun (g_another_pre _ _ _ _ _ _ _ _ _) _).mp ⟨a, b, hu, hi, ha, hb⟩
  refine eventually_weaken _ _ _ _ (fun st hs => ?_)
    (ff_aac_sbr_ctx_alloc_init_spec h_bin h_ext ac che_slot id_aac avctx f er ps sp
      (Wo ⋆ Rest) ra t h_ac h_che h_id h_sp hpre)
  rcases hs with ⟨hra, hab, ⟨h0, p, hm⟩ | ⟨h0, hm⟩⟩ | hf
  · exact Or.inl ⟨hra, hab, Or.inl ⟨h0, p, (congrFun (g_another_ok _ _ _ _ _ _ _) _).mp hm⟩⟩
  · refine Or.inl ⟨hra, hab, Or.inr ⟨h0, ?_⟩⟩
    obtain ⟨a, b, hu, hi, ⟨a1, a2, hu1, hi1, hc, he⟩, hb⟩ :=
      (congrFun (g_another_fail _ _ _ _ _ _ _ _ _) _).mp hm
    have hI : W a := hW ▸ ⟨a1, a2, hu1, hi1, ⟨f, hc⟩, he⟩
    exact (congrFun (g_another_back _ _ _ _ _ _) _).mp ⟨a, b, hu, hi, hI, hb⟩
  · exact Or.inr hf

/-- **`ff_aac_sbr_ctx_alloc_init(ac, che_slot, id_aac)` with an element already initialized**:
create a second SBR element of the same decoder.

*Before the call.* As for `ff_aac_sbr_ctx_alloc_init_spec`, except that the caller holds an
element `che₁` already initialized for `ac` (`SbrInitialized S che₁ ac`) instead of `ac->fdsp`,
its routine table and the shared data: `che₁` holds them. Memory is the disjoint union of the
regions listed in `h_mem`, one per line.

*Assumed.* As for `ff_aac_sbr_ctx_alloc_init_spec`: `SbrBinary` and the external routines'
contracts (`InitExt`).

*After, in every run.* The procedure returns to `ra` with the ABI's registers (`AbiReturn`), and
either
* the result is `0`: for some `p`, `*che_slot = p`, the new element at `p` is initialized (it now
  holds the shared part), and the first element is its own part (`SbrElemInitialized S che₁`);
  `sbr_switch_element` hands the shared part back to `che₁`; or
* the result is negative: the first element is whole again (`ac->fdsp` is unchanged), and at
  `che_slot` is what the failed allocation left (`InitFailed`). -/
theorem ff_aac_sbr_ctx_alloc_init_another_spec {S : Setup} {X : Mem 64 → Prop}
    (h_bin : SbrBinary) (h_ext : InitExt S X)
    (ac che₁ che_slot : BitVec 64) (id_aac : BitVec 32) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che_slot)
    (h_id : (t.regs.get64 .rdx).setWidth 32 = id_aac) (h_sp : t.regs.get64 .rsp = sp)
    (h_mem : t.dmem =⋆
        StackAt ra sp (initStack S.k)          -- return address; free stack below
      ⋆ SbrInitialized S che₁ ac               -- the element already initialized
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ 8 ?@ che_slot                          -- the slot for the new pointer
      ⋆ X                                      -- the allocator's and transforms' state
      ⋆ Rest) :                                -- everything else the caller owns
    Returns "ff_aac_sbr_ctx_alloc_init" t ra (fun s => AbiReturn t s ∧
      ((ret32 s = 0#32 ∧ ∃ p : BitVec 64, s.dmem =⋆
            StackAfter sp (initStack S.k)      -- the stack region, back
          ⋆ SbrInitialized S p ac              -- the new element
          ⋆ SbrElemInitialized S che₁          -- the first element's own part
          ⋆ AcFields ac avctx er ps            -- *ac's three fields
          ⋆ PtrAt che_slot p                   -- *che_slot = p
          ⋆ X
          ⋆ Rest)                              -- holds again
      ∨ ((ret32 s).toInt < 0 ∧ s.dmem =⋆
            StackAfter sp (initStack S.k)
          ⋆ SbrInitialized S che₁ ac           -- the first element, as before
          ⋆ AcFields ac avctx er ps
          ⋆ InitFailed S che_slot id_aac       -- what the failed call left
          ⋆ X
          ⋆ Rest))) :=
  init_another (sbrInitialized_eq S che₁ ac) h_bin h_ext
    che_slot id_aac avctx er ps sp Rest ra t h_ac h_che h_id h_sp h_mem

/-- **`ff_aac_sbr_ctx_alloc_init(ac, che_slot, id_aac)` with a ready element**: as
`ff_aac_sbr_ctx_alloc_init_another_spec`, when the element already there is ready
(`SbrReady`), for instance because FFmpeg sets up a new channel configuration in the middle of a
stream. Readiness is kept: on success the first element's own part is ready
(`SbrElemReady S che₁`), and on failure the first element is `SbrReady` again. -/
theorem ff_aac_sbr_ctx_alloc_init_another_ready_spec {S : Setup} {X : Mem 64 → Prop}
    (h_bin : SbrBinary) (h_ext : InitExt S X)
    (ac che₁ che_slot : BitVec 64) (id_aac : BitVec 32) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (Rest : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che_slot)
    (h_id : (t.regs.get64 .rdx).setWidth 32 = id_aac) (h_sp : t.regs.get64 .rsp = sp)
    (h_mem : t.dmem =⋆
        StackAt ra sp (initStack S.k)          -- return address; free stack below
      ⋆ SbrReady S che₁ ac                     -- the element already initialized, ready
      ⋆ AcFields ac avctx er ps                -- *ac's three fields
      ⋆ 8 ?@ che_slot                          -- the slot for the new pointer
      ⋆ X                                      -- the allocator's and transforms' state
      ⋆ Rest) :                                -- everything else the caller owns
    Returns "ff_aac_sbr_ctx_alloc_init" t ra (fun s => AbiReturn t s ∧
      ((ret32 s = 0#32 ∧ ∃ p : BitVec 64, s.dmem =⋆
            StackAfter sp (initStack S.k)      -- the stack region, back
          ⋆ SbrInitialized S p ac              -- the new element
          ⋆ SbrElemReady S che₁                -- the first element's own part, ready
          ⋆ AcFields ac avctx er ps            -- *ac's three fields
          ⋆ PtrAt che_slot p                   -- *che_slot = p
          ⋆ X
          ⋆ Rest)                              -- holds again
      ∨ ((ret32 s).toInt < 0 ∧ s.dmem =⋆
            StackAfter sp (initStack S.k)
          ⋆ SbrReady S che₁ ac                 -- the first element, as before
          ⋆ AcFields ac avctx er ps
          ⋆ InitFailed S che_slot id_aac       -- what the failed call left
          ⋆ X
          ⋆ Rest))) :=
  init_another (sbrReady_eq S che₁ ac) h_bin h_ext
    che_slot id_aac avctx er ps sp Rest ra t h_ac h_che h_id h_sp h_mem

/-! ## Memory safety, stated directly

The two readings of `Rest`, for `ff_aac_sbr_apply`. The same two corollaries follow in the same
way for each of the other four. -/

/-- **`ff_aac_sbr_apply` touches only its regions.** If memory consists of exactly the listed
regions and nothing else, every run still returns. Since an access to an address outside the
memory cannot step (the semantics has no successor for it), no run reads or writes any other
address. -/
theorem ff_aac_sbr_apply_only_its_regions {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_L : t.regs.get64 .rcx = L) (h_R : t.regs.get64 .r8 = R)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp)
    (h_out : isAligned 32 L = true ∧ isAligned 32 R = true)
    (h_mem : t.dmem =⋆
        StackAt ra sp (applyStack S.k)
      ⋆ SbrReady S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R) :                      -- and nothing else
    Returns "ff_aac_sbr_apply" t ra (fun s => AbiReturn t s ∧ s.dmem =⋆
        StackAfter sp (applyStack S.k)
      ⋆ SbrReady S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R) := by
  rw [← Std.ExtHashMap.sep_emp (StackAt ra sp _ ⋆ _ ⋆ _ ⋆ _)] at h_mem
  refine eventually_weaken _ _ _ _ (fun st hs => ?_)
    (ff_aac_sbr_apply_spec h_bin h_stk ac che L R avctx er ps sp Std.ExtHashMap.emp ra t
      h_ac h_che h_L h_R h_sp h_align h_out h_mem)
  rcases hs with ⟨hra, hab, hm⟩ | hf
  · exact Or.inl ⟨hra, hab, by rwa [Std.ExtHashMap.sep_emp] at hm⟩
  · exact Or.inr hf

/-- **`ff_aac_sbr_apply` leaves everything else unchanged.** Whatever the rest of memory holds,
as exact bytes `r`, every run returns with exactly the same bytes `r` at the same addresses. -/
theorem ff_aac_sbr_apply_keeps_the_rest {S : Setup}
    (h_bin : SbrBinary) (h_stk : StackBound S)
    (ac che L R : BitVec 64) (avctx : BitVec 64) (er ps : BitVec 32)
    (sp : BitVec 64) (r : Mem 64) (ra : Int64) (t : MachineData)
    (h_ac : t.regs.get64 .rdi = ac) (h_che : t.regs.get64 .rsi = che)
    (h_L : t.regs.get64 .rcx = L) (h_R : t.regs.get64 .r8 = R)
    (h_sp : t.regs.get64 .rsp = sp) (h_align : StackAligned sp)
    (h_out : isAligned 32 L = true ∧ isAligned 32 R = true)
    (h_mem : t.dmem =⋆
        StackAt ra sp (applyStack S.k)
      ⋆ SbrReady S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R
      ⋆ (· = r)) :                             -- the rest: exactly the bytes r
    Returns "ff_aac_sbr_apply" t ra (fun s => AbiReturn t s ∧ s.dmem =⋆
        StackAfter sp (applyStack S.k)
      ⋆ SbrReady S che ac
      ⋆ AcFields ac avctx er ps
      ⋆ OutBuffers L R
      ⋆ (· = r)) :=                            -- the same bytes r
  ff_aac_sbr_apply_spec h_bin h_stk ac che L R avctx er ps sp _ ra t
    h_ac h_che h_L h_R h_sp h_align h_out h_mem

end Kraken.Examples.Sbr.SessionBin
