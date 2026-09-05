import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath4 : List Located :=
  [opAt 3139 .JUMPDEST,
   pushAt 3140 4 873080578,
   pushAt 3141 1 32,
   opAt 3142 .MSTORE,
   pushAt 3143 4 3041660317,
   pushAt 3144 1 64,
   opAt 3145 .MSTORE,
   pushAt 3146 4 3635256273,
   pushAt 3147 1 96,
   opAt 3148 .MSTORE,
   pushAt 3149 4 3366369317,
   pushAt 3150 1 128,
   opAt 3151 .MSTORE,
   pushAt 3152 4 2877619717,
   pushAt 3153 1 160,
   opAt 3154 .MSTORE,
   opAt 3155 .POP,
   opAt 3156 .JUMP]

def bodyPath5 : List Located :=
  [opAt 3157 .JUMPDEST,
   pushAt 3158 4 3796534675,
   pushAt 3159 1 32,
   opAt 3160 .MSTORE,
   pushAt 3161 4 2687350761,
   pushAt 3162 1 64,
   opAt 3163 .MSTORE,
   pushAt 3164 4 2689944790,
   pushAt 3165 1 96,
   opAt 3166 .MSTORE,
   pushAt 3167 4 638611499,
   pushAt 3168 1 128,
   opAt 3169 .MSTORE,
   pushAt 3170 4 4094793319,
   pushAt 3171 1 160,
   opAt 3172 .MSTORE,
   opAt 3173 .POP,
   opAt 3174 .JUMP]

def bodyPath6 : List Located :=
  [opAt 3175 .JUMPDEST,
   pushAt 3176 4 3639504830,
   pushAt 3177 1 32,
   opAt 3178 .MSTORE,
   pushAt 3179 4 929905327,
   pushAt 3180 1 64,
   opAt 3181 .MSTORE,
   pushAt 3182 4 76966889,
   pushAt 3183 1 96,
   opAt 3184 .MSTORE,
   pushAt 3185 4 953753631,
   pushAt 3186 1 128,
   opAt 3187 .MSTORE,
   pushAt 3188 4 3257211883,
   pushAt 3189 1 160,
   opAt 3190 .MSTORE,
   opAt 3191 .POP,
   opAt 3192 .JUMP]

def bodyPath7 : List Located :=
  [opAt 3193 .JUMPDEST,
   pushAt 3194 4 2443344089,
   pushAt 3195 1 32,
   opAt 3196 .MSTORE,
   pushAt 3197 4 3717540601,
   pushAt 3198 1 64,
   opAt 3199 .MSTORE,
   pushAt 3200 4 207704023,
   pushAt 3201 1 96,
   opAt 3202 .MSTORE,
   pushAt 3203 4 248446432,
   pushAt 3204 1 128,
   opAt 3205 .MSTORE,
   pushAt 3206 4 3649743890,
   pushAt 3207 1 160,
   opAt 3208 .MSTORE,
   opAt 3209 .POP,
   opAt 3210 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
