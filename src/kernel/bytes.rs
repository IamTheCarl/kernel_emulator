// Copyright 2022 James Carl
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};

#[derive(Debug)]
pub enum Bytes {
    Static(&'static [u8]),
    Reference(Arc<Vec<u8>>),
    Original(Vec<u8>),
}

impl Bytes {
    // Used in unit tests.
    #[allow(unused)]
    pub fn from_static(data: &'static [u8]) -> Self {
        Self::Static(data)
    }

    // Used in unit tests.
    #[allow(unused)]
    pub fn from_vec(data: Vec<u8>) -> Self {
        Self::Original(data)
    }

    pub fn reference(data: Arc<Vec<u8>>) -> Self {
        Self::Reference(data)
    }
}

impl Clone for Bytes {
    fn clone(&self) -> Self {
        match self {
            Self::Static(data) => Self::Static(data),
            Self::Reference(data) => Self::Reference(Arc::clone(data)),
            Self::Original(data) => Self::Original(data.clone()),
        }
    }
}

impl Deref for Bytes {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        match self {
            Bytes::Static(data) => data,
            Bytes::Reference(data) => data,
            Bytes::Original(data) => data,
        }
    }
}

impl DerefMut for Bytes {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Bytes::Static(data) => {
                // Convert yourself into an original so we don't modify the static memory.
                *self = Self::Original(data.to_vec());
                self.deref_mut()
            }
            Bytes::Reference(data) => {
                // Convert yourself into an original so we don't modify the source memory.
                *self = Self::Original(Vec::clone(data));
                self.deref_mut()
            }
            Bytes::Original(data) => data.deref_mut(),
        }
    }
}

#[test]
fn from_static() {
    let data = b"test";
    let mut bytes = Bytes::from_static(data);
    assert_eq!(&*bytes, data);

    let static_clone = Bytes::clone(&bytes);
    assert_eq!(&*static_clone, data);

    // Modifcation will result in a new vector.
    let test2 = b"tset";
    bytes.copy_from_slice(test2);
    assert_eq!(&*bytes, test2);
    assert_ne!(&*static_clone, test2);
}

#[test]
fn from_vec() {
    let data = b"test";
    let vec = data.to_vec();
    let bytes = Bytes::from_vec(vec);
    assert_eq!(&*bytes, data);

    let vec_clone = Bytes::clone(&bytes);
    assert_eq!(&*vec_clone, data);
}

#[test]
fn reference() {
    let data = b"test";
    let vec = data.to_vec();
    let bytes = Bytes::reference(Arc::new(vec));
    assert_eq!(&*bytes, data);

    let mut reference = Bytes::clone(&bytes);

    assert_eq!(*reference, *bytes);

    // They should be the same pointer.
    assert_eq!(reference.as_ptr(), bytes.as_ptr());

    reference.reverse();

    // Now they should be different.
    assert_ne!(reference.as_ptr(), bytes.as_ptr());
}
