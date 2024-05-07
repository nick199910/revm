use crate::{db::Database, handler::Handler, Evm};
use std::boxed::Box;

/// EVM Handler
pub type EvmHandler<'a, T, EXT, DB> = Handler<'a, T, Evm<'a, T, EXT, DB>, EXT, DB>;

// Handle register
pub type HandleRegister<T, EXT, DB> = for<'a> fn(&mut EvmHandler<'a, T, EXT, DB>);

// Boxed handle register
pub type HandleRegisterBox<T, EXT, DB> = Box<dyn for<'a> Fn(&mut EvmHandler<'a, T, EXT, DB>)>;

pub enum HandleRegisters<T, EXT, DB: Database> {
    /// Plain function register
    Plain(HandleRegister<T, EXT, DB>),
    /// Boxed function register.
    Box(HandleRegisterBox<T, EXT, DB>),
}

impl<T, EXT, DB: Database> HandleRegisters<T, EXT, DB> {
    /// Call register function to modify EvmHandler.
    pub fn register(&self, handler: &mut EvmHandler<'_, T, EXT, DB>) {
        match self {
            HandleRegisters::Plain(f) => f(handler),
            HandleRegisters::Box(f) => f(handler),
        }
    }
}
