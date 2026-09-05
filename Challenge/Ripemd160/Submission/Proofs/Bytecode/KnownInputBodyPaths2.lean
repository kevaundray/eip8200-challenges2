import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath8 : List Located :=
  [opAt 3211 .JUMPDEST,
   pushAt 3212 4 2545269814,
   pushAt 3213 1 32,
   opAt 3214 .MSTORE,
   pushAt 3215 4 694060394,
   pushAt 3216 1 64,
   opAt 3217 .MSTORE,
   pushAt 3218 4 1242370006,
   pushAt 3219 1 96,
   opAt 3220 .MSTORE,
   pushAt 3221 4 727358371,
   pushAt 3222 1 128,
   opAt 3223 .MSTORE,
   pushAt 3224 4 2910435314,
   pushAt 3225 1 160,
   opAt 3226 .MSTORE,
   opAt 3227 .POP,
   opAt 3228 .JUMP]

def bodyPath9 : List Located :=
  [opAt 3229 .JUMPDEST,
   pushAt 3230 4 1383816819,
   pushAt 3231 1 32,
   opAt 3232 .MSTORE,
   pushAt 3233 4 2927167799,
   pushAt 3234 1 64,
   opAt 3235 .MSTORE,
   pushAt 3236 4 3917135274,
   pushAt 3237 1 96,
   opAt 3238 .MSTORE,
   pushAt 3239 4 1152436130,
   pushAt 3240 1 128,
   opAt 3241 .MSTORE,
   pushAt 3242 4 1750728161,
   pushAt 3243 1 160,
   opAt 3244 .MSTORE,
   opAt 3245 .POP,
   opAt 3246 .JUMP]

def bodyPath10 : List Located :=
  [opAt 3247 .JUMPDEST,
   pushAt 3248 4 2129352215,
   pushAt 3249 1 32,
   opAt 3250 .MSTORE,
   pushAt 3251 4 713868608,
   pushAt 3252 1 64,
   opAt 3253 .MSTORE,
   pushAt 3254 4 3614122856,
   pushAt 3255 1 96,
   opAt 3256 .MSTORE,
   pushAt 3257 4 1332659877,
   pushAt 3258 1 128,
   opAt 3259 .MSTORE,
   pushAt 3260 4 1189775218,
   pushAt 3261 1 160,
   opAt 3262 .MSTORE,
   opAt 3263 .POP,
   opAt 3264 .JUMP]

def bodyPath11 : List Located :=
  [opAt 3265 .JUMPDEST,
   pushAt 3266 4 3435206255,
   pushAt 3267 1 32,
   opAt 3268 .MSTORE,
   pushAt 3269 4 1888837243,
   pushAt 3270 1 64,
   opAt 3271 .MSTORE,
   pushAt 3272 4 4052516846,
   pushAt 3273 1 96,
   opAt 3274 .MSTORE,
   pushAt 3275 4 98219359,
   pushAt 3276 1 128,
   opAt 3277 .MSTORE,
   pushAt 3278 4 3698254713,
   pushAt 3279 1 160,
   opAt 3280 .MSTORE,
   opAt 3281 .POP,
   opAt 3282 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
