# Sentence Processing with Pushdown Automata

**UCLA LING 185A — Computational Linguistics | Winter 2025**  
**Author:** Willie (Chun Wei) Wen  
**Language:** Haskell

## Overview

How can a formal grammar represent the structure of a sentence, and what can different parsing strategies tell us about the computational demands of language processing?

This course project investigates those questions by implementing **pushdown automata (PDAs)** and converting **context-free grammars (CFGs)** into three sentence-processing strategies:

1. **Bottom-up parsing** — constructs larger constituents from recognized words and phrases.
2. **Top-down parsing** — predicts grammatical structure from the sentence's start symbol.
3. **Left-corner parsing** — combines recognition of an initial constituent with predictions about the remaining structure.

Written in Haskell, the implementation supports stack transitions, verification of transition sequences, recursive recognition (including ε-transitions), configurable stack restrictions, and comparison of parsing paths. The accompanying eight-page paper uses these implementations to discuss **syntactic ambiguity, left/right/center embedding, stack depth, and the limitations of formal grammars as models of human sentence processing**.

> **Scope:** This is a formal-language implementation and theoretical computational-linguistics project, **not** a trained NLP model or an empirical experiment measuring human reading time, neural responses, or cognitive load.

## Repository contents

```text
sentence-processing-pda/
├── PDA.hs                         # Haskell PDA/CFG definitions and implemented functions
├── NLP_Project_Paper_WILLIE.pdf   # Eight-page final paper and analysis
└── README.md                      # Documentation and usage examples
```

`PDA.hs` includes **course-provided starter definitions and demonstration grammars above the marked divider**. The transition, recognition, and CFG-to-PDA conversion functions **below** that divider are my project implementations.

## Requirements and setup

- **GHC/GHCi**, the Glasgow Haskell Compiler and interactive interpreter
- No external Haskell packages beyond the standard libraries used in `PDA.hs`

Place the files in one directory and start the interpreter:

```bash
ghci PDA.hs
```

From within GHCi, you can reload the source after changes:

```haskell
:reload
```

All examples below are expressions to enter at the **GHCi prompt**, not shell commands. The sample grammar data is already defined in `PDA.hs`; no separate dataset is needed.

## Core representations

### Pushdown automata and transitions

A transition is represented as:

```haskell
type Transition st sy = ([st], Maybe sy, [st])
type PDA st sy = ([[st]], [[st]], [Transition st sy])
```

Each transition has the form **(stack prefix to remove, optional input symbol, replacement stack prefix)**. The top of the stack is on the **left** of the Haskell list. `Just symbol` consumes a matching input symbol, whereas `Nothing` denotes an **ε-transition** that consumes no input.

`PDA` records the permitted **initial stacks**, **final stacks**, and **transitions**. A successful recognition path consumes all input and finishes in a permitted final stack.

### Context-free grammars

```haskell
type CFG nt sy = ([nt], [RewriteRule nt sy])
data RewriteRule nt sy = TRule nt sy | NTRule nt (nt, [nt])
```

`TRule` associates a nonterminal with a terminal; `NTRule` expands a nonterminal into a nonempty sequence of nonterminals. The starter code includes two example grammars:

- `cfg_anbn`: generates `aⁿbⁿ`, with **n ≥ 1**.
- `cfg_eng`: a small English-like grammar covering noun phrases, verb phrases, relative clauses, possessives, and prepositional phrases.

The separately provided `pda_anbn` example allows **n ≥ 0**, including the empty string; it is not identical to `cfg_anbn`.

## Implemented functions

| Function | Purpose |
|---|---|
| `tryTransition` | Apply a valid prefix-replacement transition to a stack, or return `Nothing` |
| `checkSequence` | Verify that each recorded transition correctly updates the stack |
| `completeSequences` | Recursively extend a transition sequence until the remaining input is consumed and a final stack is reached |
| `pdaRecognize` | Start recognition from each permitted initial stack |
| `bottomUpPDA` / `bottomUpRecognize` | Convert CFG rules into shift/reduce transitions and recognize strings |
| `topDownPDA` / `topDownRecognize` | Convert CFG rules into predict/match transitions and recognize strings |
| `leftCornerPDA` / `leftCornerRecognize` | Combine bottom-up evidence and top-down predictions using `Found` and `Predicted` stack symbols |

The recursive search explores matching **ε-transitions** and **input-consuming transitions**. Its `fn :: [st] -> Bool` argument filters **newly reached stack states**. The top-down and left-corner wrappers use a simple depth limit: `length stack <= length input + 1`.

## Worked examples

### 1. Apply a stack transition

```haskell
tryTransition ("X", Just 'a', "XA") "X"
-- Just "XA"

tryTransition ("X", Just 'a', "XA") "XAAAAA"
-- Just "XAAAAAA"

tryTransition ("X", Just 'a', "XA") "AX"
-- Nothing
```

The replacement works only when the required prefix matches the current **top of the stack**. In this function, the transition's input label is not itself checked; input matching occurs in `completeSequences`.

### 2. Check a sequence of transitions

```haskell
checkSequence seq_aabb
-- True
```

`seq_aabb` is a provided example of a consistent PDA transition trace. `checkSequence` checks **internal stack consistency**, not whether the transitions belong to a particular PDA or consume a specified input.

### 3. Recognize `aⁿbⁿ`

The demonstration automaton accepts matching runs of `a` followed by `b`:

```haskell
length (pdaRecognize pda_anbn (\_ -> True) "aabb")
-- 1

length (pdaRecognize pda_anbn (\_ -> True) "aaabbb")
-- 1

length (pdaRecognize pda_anbn (\_ -> True) "aab")
-- 0
```

You can inspect the complete path, including its evolving stack, by omitting `length`:

```haskell
pdaRecognize pda_anbn (\_ -> True) "aabb"
```

The `completeSequences` function can also continue from an explicitly supplied starting sequence:

```haskell
length (completeSequences pda_anbn (\_ -> True) (Start "X") "aabb")
-- 1
```

### 4. Find multiple analyses of an ambiguous input

The supplied `pda_ambig` recognizes a string of `a` symbols through **two different successful transition paths**:

```haskell
length (pdaRecognize pda_ambig (\_ -> True) "aaa")
-- 2
```

Restricting the search to stacks that do **not** contain state `1` eliminates one path:

```haskell
length (pdaRecognize pda_ambig (\s -> not (elem 1 s)) "aaa")
-- 1
```

This illustrates why a recognizer can return **multiple transition sequences for the same surface string**, and how a state constraint can prune the search. It does not by itself assign linguistic plausibility or probabilities to the analyses.

### 5. Compare the three CFG-based parsing strategies

For `cfg_anbn`, each implementation recognizes the valid string `"aabb"`:

```haskell
length (bottomUpRecognize cfg_anbn "aabb")
-- 1

length (topDownRecognize cfg_anbn "aabb")
-- 1

length (leftCornerRecognize cfg_anbn "aabb")
-- 1

length (bottomUpRecognize cfg_anbn "aab")
-- 0
```

To inspect how a top-down parser predicts structure and consumes symbols, run:

```haskell
topDownRecognize cfg_anbn "aabb"
```

An example of its transition trace is:

```text
---                           [0]
([0],Nothing,[1,0,2])        [1,0,2]
([1],Just 'a',[])            [0,2]
([0],Nothing,[1,2])          [1,2,2]
([1],Just 'a',[])            [2,2]
([2],Just 'b',[])            [2]
([2],Just 'b',[])            []
```

The `Nothing` steps expand predicted nonterminals without consuming a letter. The `Just` steps match actual input letters and shorten the stack.

### 6. Explore structural ambiguity in English

Consider:

> John saw the baby with the telescope.

The simplified grammar permits two analyses involving different attachments of **“with the telescope”**. Compare all three parsers:

```haskell
let sentence = words "John saw the baby with the telescope"

length (bottomUpRecognize cfg_eng sentence)
-- 2

length (topDownRecognize cfg_eng sentence)
-- 2

length (leftCornerRecognize cfg_eng sentence)
-- 2
```

Each result counts **accepted transition sequences** under the configured recognizer. These paths represent alternative structural analyses of the string in this grammar; they are not measured human interpretations.

### 7. Examine embedded sentences and stack depth

Three constructions discussed in the paper can be explored with the provided English-like CFG:

| Structure | Example | Central question |
|---|---|---|
| Left embedding | `the boss 's actor 's baby won` | What happens as noun-phrase structure recursively builds on the left? |
| Right embedding | `John met the actor that won the award` | How does processing handle a continuing clause? |
| Center embedding | `the actor the boy the baby saw met won` | How many predicted or unfinished constituents must be maintained? |

**Tokenization note:** The grammar recognizes the possessive marker as the separate token `'s`. Use `"boss 's"`, not `"boss's"`, with the simple `words` tokenizer.

For example:

```haskell
let center = words "the actor the boy the baby saw met won"

length (bottomUpRecognize cfg_eng center)
-- 1

length (topDownRecognize cfg_eng center)
-- 1

length (leftCornerRecognize cfg_eng center)
-- 1
```

The supplied output format displays the stack **after each transition**. To measure stack depth across a returned path during a GHCi session, define:

```haskell
:{
let stackDepths (Start s) = [length s]
    stackDepths (previous ::: (_, s)) = stackDepths previous ++ [length s]
:}
```

Then, for example:

```haskell
map stackDepths (topDownRecognize cfg_anbn "aabb")
-- [[1,3,2,3,2,1,0]]

map (maximum . stackDepths) (topDownRecognize cfg_anbn "aabb")
-- [3]
```

You can apply the same helper to the three English parsing strategies and compare **peak stack depth** or inspect the complete sequence of depths. The project does **not** include a separate benchmark script or numerical human-memory data; these are measurements of the **formal parser's stack**, not direct measurements of working memory.

## How the three parsing strategies differ

| Strategy | Construction method | General intuition |
|---|---|---|
| **Bottom-up** | Shift terminal categories onto the stack; reduce recognized sequences using CFG rules | Build structure from observed input |
| **Top-down** | Predict the right-hand side of a grammar rule; match terminals against the input | Use a grammatical hypothesis to guide processing |
| **Left-corner** | Register a recognized leftmost constituent, then connect it to predicted structure | Combine observed evidence with predictions |

The project paper discusses the implications of these strategies for **left-, right-, and center-embedded constructions**. Center embedding is particularly interesting because multiple constituents may remain unresolved while additional material is processed. The stack serves as a **formal model of retained syntactic structure**; whether its size predicts human processing difficulty is a separate empirical question.

## Design choices and limitations

- **Explicit ε-transition search.** `completeSequences` considers transitions that consume no input as well as those that match the next input symbol.
- **Configurable pruning.** The `fn` predicate filters newly generated stacks. The two predictive recognizers use `length input + 1` as a practical search bound; this is a **heuristic**, not a universal completeness guarantee or an established cognitive memory threshold. Some valid derivations could be pruned under a restrictive bound.
- **Depth-first exploration.** The order of returned paths depends on the order of transitions and recursive exploration. The program does not implement a psychological preference model, probability distribution, or a learned ranking of parses.
- **Potential nontermination.** The recognizer does not implement general cycle detection or memoization. Arbitrary grammars/PDAs with unproductive ε-cycles can cause nonterminating searches, even with a stack-length restriction.
- **Restricted CFG formalism.** The supplied `NTRule` representation requires a nonempty right-hand side; CFG rules of the form `A → ε` are not implemented.
- **No parse-tree export.** The program returns **transition traces**, not visual syntax trees. Trees could be reconstructed from traces in future work.
- **Simplified language coverage.** `cfg_eng` is a small hand-specified grammar, not a broad-coverage English parser.
- **Interpretive scope.** Discussion of memory limitations, ambiguity, and garden-path effects in the accompanying paper is **theoretical**; no behavioral or neuroscience experiments were conducted for this project.

## Potential extensions

1. Detect repeated parser configurations or use memoization to avoid unproductive loops.
2. Construct parse trees from successful transition sequences.
3. Compare peak stack depth and search cost systematically across embedding types and sentence lengths.
4. Distinguish guaranteed-complete recognition from search with heuristic pruning.
5. Evaluate parsing predictions against behavioral data (e.g., reading times or comprehension accuracy), rather than treating stack size alone as a cognitive explanation.

## Paper and attribution

**Willie (Chun Wei) Wen.** *Final Project: Pushdown Automata and Sentence-Processing.* UCLA LING 185A, Winter 2025. See [`NLP_Project_Paper_WILLIE.pdf`](NLP_Project_Paper_WILLIE.pdf) for the full implementation discussion, structural analyses, and reflection.

**Course context:** Project instructions and the original PDA/CFG starter framework were provided by **Tim Hunter**, UCLA LING 185A (Winter 2025). The marked implementation section of `PDA.hs` contains my solutions to the project tasks. Examples and terminology in this README are aligned with that assignment and the accompanying paper.
