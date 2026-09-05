import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def selectorGroup0 : List Located :=
  [opAt 2985 (.Dup ⟨2, by decide⟩),
   pushAt 2986 0 0,
   opAt 2987 .EQ,
   pushAt 2988 2 6216,
   opAt 2989 .JUMPI]

def selectorGroup1 : List Located :=
  [opAt 2990 (.Dup ⟨2, by decide⟩),
   pushAt 2991 1 64,
   opAt 2992 .EQ,
   pushAt 2993 2 6259,
   opAt 2994 .JUMPI]

def selectorGroup2 : List Located :=
  [opAt 2995 (.Dup ⟨2, by decide⟩),
   pushAt 2996 1 128,
   opAt 2997 .EQ,
   pushAt 2998 2 6302,
   opAt 2999 .JUMPI]

def selectorGroup3 : List Located :=
  [opAt 3000 (.Dup ⟨2, by decide⟩),
   pushAt 3001 1 192,
   opAt 3002 .EQ,
   pushAt 3003 2 6345,
   opAt 3004 .JUMPI]

def selectorGroup4 : List Located :=
  [opAt 3005 (.Dup ⟨2, by decide⟩),
   pushAt 3006 2 256,
   opAt 3007 .EQ,
   pushAt 3008 2 6388,
   opAt 3009 .JUMPI]

def selectorGroup5 : List Located :=
  [opAt 3010 (.Dup ⟨2, by decide⟩),
   pushAt 3011 2 320,
   opAt 3012 .EQ,
   pushAt 3013 2 6431,
   opAt 3014 .JUMPI]

def selectorGroup6 : List Located :=
  [opAt 3015 (.Dup ⟨2, by decide⟩),
   pushAt 3016 2 384,
   opAt 3017 .EQ,
   pushAt 3018 2 6474,
   opAt 3019 .JUMPI]

def selectorGroup7 : List Located :=
  [opAt 3020 (.Dup ⟨2, by decide⟩),
   pushAt 3021 2 448,
   opAt 3022 .EQ,
   pushAt 3023 2 6517,
   opAt 3024 .JUMPI]

def selectorGroup8 : List Located :=
  [opAt 3025 (.Dup ⟨2, by decide⟩),
   pushAt 3026 2 512,
   opAt 3027 .EQ,
   pushAt 3028 2 6560,
   opAt 3029 .JUMPI]

def selectorGroup9 : List Located :=
  [opAt 3030 (.Dup ⟨2, by decide⟩),
   pushAt 3031 2 576,
   opAt 3032 .EQ,
   pushAt 3033 2 6603,
   opAt 3034 .JUMPI]

def selectorGroup10 : List Located :=
  [opAt 3035 (.Dup ⟨2, by decide⟩),
   pushAt 3036 2 640,
   opAt 3037 .EQ,
   pushAt 3038 2 6646,
   opAt 3039 .JUMPI]

def selectorGroup11 : List Located :=
  [opAt 3040 (.Dup ⟨2, by decide⟩),
   pushAt 3041 2 704,
   opAt 3042 .EQ,
   pushAt 3043 2 6689,
   opAt 3044 .JUMPI]

def selectorGroup12 : List Located :=
  [opAt 3045 (.Dup ⟨2, by decide⟩),
   pushAt 3046 2 768,
   opAt 3047 .EQ,
   pushAt 3048 2 6732,
   opAt 3049 .JUMPI]

def selectorGroup13 : List Located :=
  [opAt 3050 (.Dup ⟨2, by decide⟩),
   pushAt 3051 2 832,
   opAt 3052 .EQ,
   pushAt 3053 2 6775,
   opAt 3054 .JUMPI]

def selectorGroup14 : List Located :=
  [opAt 3055 (.Dup ⟨2, by decide⟩),
   pushAt 3056 2 896,
   opAt 3057 .EQ,
   pushAt 3058 2 6818,
   opAt 3059 .JUMPI]

def selectorGroup15 : List Located :=
  [opAt 3060 (.Dup ⟨2, by decide⟩),
   pushAt 3061 2 960,
   opAt 3062 .EQ,
   pushAt 3063 2 6861,
   opAt 3064 .JUMPI]

def selectorPath0 : List Located := selectorGroup0
def selectorPath1 : List Located := selectorGroup0 ++ selectorGroup1
def selectorPath2 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2
def selectorPath3 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3
def selectorPath4 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4
def selectorPath5 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5
def selectorPath6 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6
def selectorPath7 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7
def selectorPath8 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8
def selectorPath9 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9
def selectorPath10 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10
def selectorPath11 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11
def selectorPath12 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11 ++ selectorGroup12
def selectorPath13 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11 ++ selectorGroup12 ++ selectorGroup13
def selectorPath14 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11 ++ selectorGroup12 ++ selectorGroup13 ++ selectorGroup14
def selectorPath15 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11 ++ selectorGroup12 ++ selectorGroup13 ++ selectorGroup14 ++ selectorGroup15

def selectorPath (i : Nat) : List Located :=
  match i with
  | 0 => selectorPath0
  | 1 => selectorPath1
  | 2 => selectorPath2
  | 3 => selectorPath3
  | 4 => selectorPath4
  | 5 => selectorPath5
  | 6 => selectorPath6
  | 7 => selectorPath7
  | 8 => selectorPath8
  | 9 => selectorPath9
  | 10 => selectorPath10
  | 11 => selectorPath11
  | 12 => selectorPath12
  | 13 => selectorPath13
  | 14 => selectorPath14
  | _ => selectorPath15

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
