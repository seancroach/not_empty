#[cfg(feature = "alloc")]
extern crate alloc;

macro_rules! import {
    ($root:ident) => {
        pub use $root::{
            borrow::{Borrow, BorrowMut, Cow, ToOwned},
            boxed::Box,
            collections::{BinaryHeap, TryReserveError, VecDeque},
            rc::Rc,
            string::String,
            sync::Arc,
            vec::{self, Vec},
        };
    };
}

#[cfg(feature = "alloc")]
import!(alloc);
#[cfg(feature = "std")]
import!(std);

#[cfg(feature = "std")]
pub use std::{
    io::{self, BufRead, Read, Write},
    net::{SocketAddr, ToSocketAddrs},
    ffi::CString,
};
