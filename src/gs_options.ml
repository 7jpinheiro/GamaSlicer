
module Self = 
  Plugin.Register
    (struct
       let name = "gamaSlicer" 
       let shortname = "gamaSlicer"
       let help = "A frama-c plugin that implements assertion based slicing"
     end)


 module SliceType =
  Self.String
    (struct
       let option_name = "-slice-type"
       let arg_name = "slice_type"
       let help = "Type of slice : post : prec : spec"
       let default = "-post"
     end)