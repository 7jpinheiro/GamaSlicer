
module Self = 
  Plugin.Register
    (struct
       let name = "gamaSlicer" 
       let shortname = "gamaSlicer"
       let help = "A frama-c plugin that implements assertion based slicing"
     end)