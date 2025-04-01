module PDA where

------------------------------------------------------------------
-- Setup for PDAs

type Transition st sy = ([st], Maybe sy, [st])
type PDA st sy = ([[st]], [[st]], [Transition st sy])

data TransitionSeq st sy = Start [st] | (TransitionSeq st sy) ::: (Transition st sy, [st])

pda_anbn :: PDA Char Char
pda_anbn = (["X"], ["Y"], 
            [("X", Just 'a', "XA"), ("X", Nothing, "Y"), ("YA", Just 'b', "Y")]
           )

pda_ambig :: PDA Int Char
pda_ambig = ([[0]], [[3]], [([0], Just 'a', [0]), 
                            ([0], Just 'a', [1]), 
                            ([0], Just 'a', [2]), 
                            ([1], Just 'a', [3]), 
                            ([2], Just 'a', [3])
                           ]
            )

seq_aabb :: TransitionSeq Char Char
seq_aabb = Start "X" ::: (("X", Just 'a', "XA") , "XA")
                     ::: (("X", Just 'a', "XA") , "XAA")
                     ::: (("X", Nothing, "Y")   , "YAA")
                     ::: (("YA", Just 'b', "Y") , "YA")
                     ::: (("YA", Just 'b', "Y") , "Y")

resultStack :: TransitionSeq st sy -> [st]
resultStack seq =
    case seq of
    Start s       -> s
    seq':::(tr,s) -> s

-- Stack symbols for left-corner processing.
data LCS nt = Predicted nt | Found nt deriving Eq

-- You can ignore this. It's the code that creates the friendly-looking 
-- displays for transition sequences.
instance (Show st, Show sy) => Show (TransitionSeq st sy) where
    show seq =
        let pad n s = s ++ replicate (n - length s) ' ' in
        let width = 30 in
        case seq of
        Start s         -> pad width "---" ++ show s
        seq' ::: (tr,s) -> show seq' ++ "\n" ++ pad width (show tr) ++ show s
    showList [] = (show ([] :: [()]) ++)
    showList (seq:[]) = (("\n" ++ show seq ++ "\n") ++)
    showList (seq:seqs) = (("\n" ++ show seq ++ "\n") ++) . (showList seqs)

-- You can also ignore this.
instance Show nt => Show (LCS nt) where
    show (Predicted nt) = show nt ++ "*"
    show (Found nt) = show nt

------------------------------------------------------------------
-- Setup for CFGs

type CFG nt sy = ([nt], [RewriteRule nt sy])
data RewriteRule nt sy = TRule nt sy | NTRule nt (nt,[nt]) deriving (Show,Eq)
data Cat = S | NP | VP | POSS | N | D | SRC | ORC | PP | P | V | THAT deriving (Show,Eq)

cfg_eng :: CFG Cat String
cfg_eng = ([S], [NTRule S (NP,[VP]), 
                 NTRule NP (NP,[POSS,N]), 
                 NTRule NP (D,[N]), 
                 NTRule NP (D,[N,SRC]), 
                 NTRule NP (D,[N,ORC]), 
                 NTRule NP (D,[N,PP]), 
                 NTRule VP (V,[]), 
                 NTRule VP (V,[NP]), 
                 NTRule VP (VP,[PP]), 
                 NTRule SRC (THAT,[VP]), 
                 NTRule ORC (NP,[V]), 
                 NTRule PP (P,[NP])
                ] ++
                map (\w -> TRule N w)  ["baby","boy","actor","boss","award","telescope"] ++
                map (\w -> TRule NP w) ["Mary","John"] ++
                map (\w -> TRule V w)  ["met","saw","won"] ++
                map (\w -> TRule P w)  ["on","with"] ++
                [TRule D "the", TRule THAT "that", TRule POSS "'s"]
          )

cfg_anbn :: CFG Int Char
cfg_anbn = ([0], [NTRule 0 (1,[0,2]), NTRule 0 (1,[2]), TRule 1 'a', TRule 2 'b'])

------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.

-- | Attempts to apply a PDA transition to the current stack.
-- If the 'popped' prefix matches the top of the stack, returns the new stack with 'pushed' added.
tryTransition :: Eq st => Transition st sy -> [st] -> Maybe [st]
-- Simulates a transition on a stack. If the stack begins with the 'popped' prefix, applies the transition and returns the new stack.
tryTransition (popped, _, pushed) stack
    | popped `isPrefixOf` stack = Just (pushed ++ drop (length popped) stack)
    | otherwise = Nothing
  where
    isPrefixOf :: (Eq a) => [a] -> [a] -> Bool
    isPrefixOf [] _      = True
    isPrefixOf _  []     = False
    isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys


-- | Verifies that each transition in the sequence correctly updates the stack.
-- Does not check if transitions are valid for a particular PDA, only stack consistency.
checkSequence :: (Eq st) => TransitionSeq st sy -> Bool
-- Checks if the transition sequence is internally consistent with stack updates (ignores PDA constraints).
checkSequence (Start s) = True
checkSequence (seq' ::: (tr, s')) =
    case tryTransition tr (resultStack seq') of
        Just s  -> s == s' && checkSequence seq'
        Nothing -> False

-- | Recursively explores all valid ways to extend a given transition sequence so that
-- the PDA consumes the remaining input string and ends in a valid final stack state.
-- Handles both input-consuming and epsilon transitions, filtering paths via a stack constraint.
completeSequences :: (Eq st, Eq sy) =>
  PDA st sy -> ([st] -> Bool) -> TransitionSeq st sy -> [sy] -> [TransitionSeq st sy]
-- Recursively generates all valid completions of a given transition sequence that accept the input string under a stack constraint.
completeSequences pda@(_, finalStacks, delta) fn seq w =
  let currentStack = resultStack seq
  in case w of
    [] ->
      let base = if currentStack `elem` finalStacks then [seq] else []
          epsMoves = [ completeSequences pda fn (seq ::: (tr, ns)) []
                      | tr@(_, Nothing, _) <- delta,
                        Just ns <- [tryTransition tr currentStack],
                        fn ns ]
      in base ++ concat epsMoves
    
    (a:as) ->
      let
          epsMoves = [ completeSequences pda fn (seq ::: (tr, ns)) (a:as)
                      | tr@(_, Nothing, _) <- delta,
                        Just ns <- [tryTransition tr currentStack],
                        fn ns ]
          
          inputMoves = [ completeSequences pda fn (seq ::: (tr, ns)) as
                         | tr@(_, Just b, _) <- delta,
                           Just ns <- [tryTransition tr currentStack],
                           fn ns,
                           b == a ]
      in concat (epsMoves ++ inputMoves)

pdaRecognize :: (Eq st, Eq sy) => PDA st sy -> ([st] -> Bool) -> [sy] -> [TransitionSeq st sy]
-- Runs a PDA on an input string and returns all valid transition sequences starting from each initial stack.
pdaRecognize pda@(initStacks, _, _) fn w =
  concat [ completeSequences pda fn (Start s) w | s <- initStacks ]

bottomUpPDA :: CFG nt sy -> PDA nt sy
-- Converts a CFG into a bottom-up PDA that uses shift-reduce strategy to build structure from terminals upward.
bottomUpPDA (startNonterms, rules) = (initial, finals, transitions)
  where
    initial = [[]]
    finals  = [[s] | s <- startNonterms]
    shift = [ ([], Just sym, [lhs])
                      | TRule lhs sym <- rules ]
    reduce = [ (reverse nts ++ [r], Nothing, [lhs])
                        | NTRule lhs (r, nts) <- rules ]
    transitions = reduce ++ shift

bottomUpRecognize :: (Eq nt, Eq sy) => CFG nt sy -> [sy] -> [TransitionSeq nt sy]
-- Recognizes input using bottom-up PDA with no out-of-bounds constraint.
bottomUpRecognize cfg w = pdaRecognize (bottomUpPDA cfg) (\_ -> True) w

topDownPDA :: CFG nt sy -> PDA nt sy
-- Converts a CFG into a top-down PDA that predicts structure from the start symbol downward.
topDownPDA (startSymbols, rules) = (initial, final, transitions)
  where
    initial = [[s] | s <- startSymbols]
    final = [[]]
    match = [ ([nt], Just terminal, []) 
            | TRule nt terminal <- rules ]
    predict = [ ([nt], Nothing, firstSym : restSyms) 
              | NTRule nt (firstSym, restSyms) <- rules ]
    transitions = match ++ predict

topDownRecognize :: (Eq nt, Eq sy) => CFG nt sy -> [sy] -> [TransitionSeq nt sy]
-- Recognizes input using a top-down PDA, with a basic stack-length constraint to avoid infinite prediction.
topDownRecognize cfg input =
    let pda@(startStacks, _, _) = topDownPDA cfg
        isValidStack stack = length stack <= length input + 1
    in pdaRecognize pda isValidStack input

leftCornerPDA :: CFG nt sy -> PDA (LCS nt) sy
-- Constructs a left-corner PDA which recognizes input by combining bottom-up evidence with top-down prediction.
leftCornerPDA (startSymbols, rules) = (initial, finals, transitions)
  where
    initial = [ [Predicted s] | s <- startSymbols ]
    finals  = [ [] ]
    shiftTrans =
      [ ([], Just sym, [Found lhs])
      | TRule lhs sym <- rules ]
    matchTrans =
      [ ([Predicted lhs], Just sym, [])
      | TRule lhs sym <- rules ]
    lcPredictTrans =
      [ ([Found first], Nothing, (map Predicted rest) ++ [Found lhs])
      | NTRule lhs (first, rest) <- rules ]
    lcConnectTrans =
      [ ([Found first, Predicted lhs], Nothing, map Predicted rest)
      | NTRule lhs (first, rest) <- rules ]
    transitions = matchTrans ++ shiftTrans ++ lcPredictTrans ++ lcConnectTrans

leftCornerRecognize :: (Eq nt, Eq sy) => CFG nt sy -> [sy] -> [TransitionSeq (LCS nt) sy]
-- Recognizes input using a left-corner PDA with a shallow stack constraint.
leftCornerRecognize cfg input =
    pdaRecognize (leftCornerPDA cfg) (\stack -> length stack <= length input + 1) input










