use std::ops::{Deref, DerefMut};

/// "user-space" implementation of something like `defer`.
///
/// stolen from
/// https://github.com/torvalds/linux/blob/cca7a0aae8958c9b1cd14116cb8b2f22ace2205e/rust/kernel/types.rs#L220
pub struct ScopeGuard<T, F: FnOnce(T)>(Option<(T, F)>);

impl ScopeGuard<(), fn(())> {
    /// the return must be bound to a named variable (e.g., `let _guard = ...`).
    ///
    /// NOTE: there is a significant difference between `let _ = ...` and `let _guard = ...`; in the
    /// former, whatever you put in place of `...` is dropped immediately, while in the latter, it's
    /// dropped when _guard goes out scope.
    #[must_use]
    pub fn new(cleanup: impl FnOnce()) -> ScopeGuard<(), impl FnOnce(())> {
        ScopeGuard::new_with_data((), |_| cleanup())
    }
}

impl<T, F: FnOnce(T)> ScopeGuard<T, F> {
    #[must_use]
    pub fn new_with_data(data: T, cleanup: F) -> Self {
        Self(Some((data, cleanup)))
    }

    /// prevents the cleanup function from running and returns the guarded data.
    pub fn dismiss(mut self) -> T {
        self.0.take().unwrap().0
    }
}

impl<T, F: FnOnce(T)> Drop for ScopeGuard<T, F> {
    fn drop(&mut self) {
        if let Some((data, cleanup)) = self.0.take() {
            cleanup(data);
        }
    }
}

impl<T, F: FnOnce(T)> Deref for ScopeGuard<T, F> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0.as_ref().unwrap().0
    }
}

impl<T, F: FnOnce(T)> DerefMut for ScopeGuard<T, F> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0.as_mut().unwrap().0
    }
}

#[test]
fn test_scopeguard() {
    let drops = std::cell::Cell::new(0);
    {
        let _guard = ScopeGuard::new(|| drops.set(1));
        assert_eq!(drops.get(), 0);
    }
    assert_eq!(drops.get(), 1);
}
