//! Share functions between modules
//!
//!

use std::hash::Hash;
use std::collections::HashMap;

pub fn insert_into_env<K: Eq + Hash, V>(env: &mut Vec<HashMap<K, V>>, key: K, value: V) -> () {
    match env.last_mut() {
        Some(env) => {env.insert(key, value);},
        None => ()
    };
}

pub fn get_from_env<K: Eq + Hash, V: Clone>(
    env_stack: &Vec<HashMap<K, V>>,
    id: K,
) -> Option<V> {
    for env in env_stack.iter().rev() {
        match env.get(&id) {
            Some(class) => return Some(class.clone()),
            None => (),
        }
    }
    return None;
}
