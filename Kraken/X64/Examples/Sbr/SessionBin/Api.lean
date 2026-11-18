import Kraken.X64.Examples.Sbr.SessionBin.Top

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

## What is not claimed

* **Functional correctness.** Output buffers, bitstream bytes and the element's contents are owned
  but unspecified.
* **When a trap happens.** The theorems allow a trap; they do not say for which inputs.
* **Teardown.** No entry point gives back the element or the shared data; there is no theorem for
  `ff_aac_sbr_ctx_close`.
* **More than one element.** The element owns the shared data, so a second init's precondition
  cannot be met while one is live.
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

/-- A ready element is initialized: after a successful parse or `ff_aac_sbr_config_usac`, the
element may be parsed again. -/
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
