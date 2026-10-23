//! Shared byte assembly for raw layout helpers.

pub(crate) fn append(output: &mut Vec<u8>, bytes: &[u8]) {
    let mut index = 0;
    while index < bytes.len() {
        output.push(bytes[index]);
        index += 1;
    }
}
