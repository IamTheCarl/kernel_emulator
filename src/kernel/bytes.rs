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
    pub fn from_static(data: &'static [u8]) -> Self {
        Self::Static(data)
    }

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
