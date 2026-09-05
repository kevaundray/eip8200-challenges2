import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath0 : List Located :=
  [opAt 3067 .JUMPDEST,
   pushAt 3068 4 3559078384,
   pushAt 3069 1 32,
   opAt 3070 .MSTORE,
   pushAt 3071 4 3462111087,
   pushAt 3072 1 64,
   opAt 3073 .MSTORE,
   pushAt 3074 4 678731893,
   pushAt 3075 1 96,
   opAt 3076 .MSTORE,
   pushAt 3077 4 3748113137,
   pushAt 3078 1 128,
   opAt 3079 .MSTORE,
   pushAt 3080 4 3334585884,
   pushAt 3081 1 160,
   opAt 3082 .MSTORE,
   opAt 3083 .POP,
   opAt 3084 .JUMP]

def bodyPath1 : List Located :=
  [opAt 3085 .JUMPDEST,
   pushAt 3086 4 340062591,
   pushAt 3087 1 32,
   opAt 3088 .MSTORE,
   pushAt 3089 4 1172984202,
   pushAt 3090 1 64,
   opAt 3091 .MSTORE,
   pushAt 3092 4 2201192442,
   pushAt 3093 1 96,
   opAt 3094 .MSTORE,
   pushAt 3095 4 3574458117,
   pushAt 3096 1 128,
   opAt 3097 .MSTORE,
   pushAt 3098 4 2363114424,
   pushAt 3099 1 160,
   opAt 3100 .MSTORE,
   opAt 3101 .POP,
   opAt 3102 .JUMP]

def bodyPath2 : List Located :=
  [opAt 3103 .JUMPDEST,
   pushAt 3104 4 252128912,
   pushAt 3105 1 32,
   opAt 3106 .MSTORE,
   pushAt 3107 4 1375323409,
   pushAt 3108 1 64,
   opAt 3109 .MSTORE,
   pushAt 3110 4 388551893,
   pushAt 3111 1 96,
   opAt 3112 .MSTORE,
   pushAt 3113 4 2965778249,
   pushAt 3114 1 128,
   opAt 3115 .MSTORE,
   pushAt 3116 4 2859683445,
   pushAt 3117 1 160,
   opAt 3118 .MSTORE,
   opAt 3119 .POP,
   opAt 3120 .JUMP]

def bodyPath3 : List Located :=
  [opAt 3121 .JUMPDEST,
   pushAt 3122 4 574200444,
   pushAt 3123 1 32,
   opAt 3124 .MSTORE,
   pushAt 3125 4 4203611133,
   pushAt 3126 1 64,
   opAt 3127 .MSTORE,
   pushAt 3128 4 2300602179,
   pushAt 3129 1 96,
   opAt 3130 .MSTORE,
   pushAt 3131 4 140662182,
   pushAt 3132 1 128,
   opAt 3133 .MSTORE,
   pushAt 3134 4 1945316582,
   pushAt 3135 1 160,
   opAt 3136 .MSTORE,
   opAt 3137 .POP,
   opAt 3138 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
