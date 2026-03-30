use std::ops::{Deref, DerefMut};

/// "user-space" implementation of something like `defer`.
///
/// stolen from
/// <https://github.com/torvalds/linux/blob/cca7a0aae8958c9b1cd14116cb8b2f22ace2205e/rust/kernel/types.rs#L220>.
/// originally called ScopeGuard.
///
/// rust now has it's own ScopeGuard thingie which is called DropGuard. the DropGuard name makese
/// more senset o me then ScopeGuard because technically this is not restricted to being in a
/// scope-scope; you can easilly put it into struct for example, etc.
pub struct DropGuard<T, F: FnOnce(T)>(Option<(T, F)>);

impl DropGuard<(), fn(())> {
    /// the return must be bound to a named variable (e.g., `let _guard = ...`).
    ///
    /// NOTE: there is a significant difference between `let _ = ...` and `let _guard = ...`; in the
    /// former, whatever you put in place of `...` is dropped immediately, while in the latter, it's
    /// dropped when _guard goes out scope.
    #[must_use]
    pub fn new(cleanup: impl FnOnce()) -> DropGuard<(), impl FnOnce(())> {
        DropGuard::new_with_data((), |_| cleanup())
    }
}

impl<T, F: FnOnce(T)> DropGuard<T, F> {
    // TODO: consider renaming DropGuard's new_with_data into with_data.
    #[must_use]
    pub fn new_with_data(data: T, cleanup: F) -> Self {
        Self(Some((data, cleanup)))
    }

    /// prevents the cleanup function from running and returns the guarded data.
    pub fn dismiss(mut self) -> T {
        self.0.take().unwrap().0
    }
}

impl<T, F: FnOnce(T)> Drop for DropGuard<T, F> {
    fn drop(&mut self) {
        if let Some((data, cleanup)) = self.0.take() {
            cleanup(data);
        }
    }
}

impl<T, F: FnOnce(T)> Deref for DropGuard<T, F> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0.as_ref().unwrap().0
    }
}

impl<T, F: FnOnce(T)> DerefMut for DropGuard<T, F> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0.as_mut().unwrap().0
    }
}

#[test]
fn test_dropguard() {
    let drops = std::cell::Cell::new(0);
    {
        let _guard = DropGuard::new(|| drops.set(1));
        assert_eq!(drops.get(), 0);
    }
    assert_eq!(drops.get(), 1);
}
