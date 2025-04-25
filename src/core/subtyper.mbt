///|
priv trait Subtyper {
  subtype(Self, Type, Type, Context) -> Bool
  join(Self, Type, Type, Context) -> Type
  meet(Self, Type, Type, Context) -> Type!NoRuleApplies
}

///|
let full : Full = Full::{  }

///|
let kernel : Kernel = Kernel::{  }

///|
let completely_bounded : CompletelyBounded = CompletelyBounded::{  }

///|
let subtyper : Ref[&Subtyper] = Ref::new(full)

///|
pub fn set_mode!(_mode : String) -> Unit {
  match _mode.to_lower() {
    "full" => subtyper.val = full
    "kernel" => subtyper.val = kernel
    "completelybounded" => subtyper.val = completely_bounded
    _ => @info.error_info!("subtyping mode \{_mode} is not supported")
  }
}
