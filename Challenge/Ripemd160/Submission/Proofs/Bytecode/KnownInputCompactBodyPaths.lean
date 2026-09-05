import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths

open KnownInputCompactPaths

def prePath : List Located :=
  [opAt 2866 (.Dup ⟨2, by decide⟩),
   pushAt 2867 1 6,
   opAt 2868 .SHR,
   pushAt 2869 1 21,
   opAt 2870 .MUL,
   pushAt 2871 2 4958,
   opAt 2872 .ADD,
   pushAt 2873 1 20,
   opAt 2874 (.Swap ⟨0, by decide⟩),
   pushAt 2875 0 0]

def postPath : List Located :=
  [pushAt 2877 0 0,
   opAt 2878 .MLOAD,
   pushAt 2879 1 224,
   opAt 2880 .SHR,
   pushAt 2881 1 32,
   opAt 2882 .MSTORE,
   pushAt 2883 1 4,
   opAt 2884 .MLOAD,
   pushAt 2885 1 224,
   opAt 2886 .SHR,
   pushAt 2887 1 64,
   opAt 2888 .MSTORE,
   pushAt 2889 1 8,
   opAt 2890 .MLOAD,
   pushAt 2891 1 224,
   opAt 2892 .SHR,
   pushAt 2893 1 96,
   opAt 2894 .MSTORE,
   pushAt 2895 1 12,
   opAt 2896 .MLOAD,
   pushAt 2897 1 224,
   opAt 2898 .SHR,
   pushAt 2899 1 128,
   opAt 2900 .MSTORE,
   pushAt 2901 1 16,
   opAt 2902 .MLOAD,
   pushAt 2903 1 224,
   opAt 2904 .SHR,
   pushAt 2905 1 160,
   opAt 2906 .MSTORE,
   opAt 2907 .POP,
   opAt 2908 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths
