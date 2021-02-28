#[derive(Debug, Clone)]
pub struct AssocVec<K, V> {
	data: Vec<(K, V)>
}

impl<K: Eq + PartialEq, V> AssocVec<K, V> {
	pub fn new() -> Self {
		AssocVec { data: Vec::new() }
	}

	pub fn contains_key(&self, sk: K) -> bool {
		for (k, v) in &self.data {
			if *k == sk {
				return true;
			}
		}
		false
	}

	pub fn insert(&mut self, ik: K, iv: V) {
		for (k, ref mut v) in &mut self.data {
			if *k == ik {
				*v = iv;
				return;
			}
		}
		self.data.push((ik, iv));
	}

	pub fn with(mut self, k: K, v: V) -> Self {
		self.insert(k, v);
		self
	}

	pub fn get(&self, sk: K) -> Option<&V> {
		for (k, v) in &self.data {
			if *k == sk {
				return Some(v);
			}
		}
		None
	}

	pub fn len(&self) -> usize {
		self.data.len()
	}

	pub fn iter(&self) -> AssocVecIterator<'_, K, V> {
		AssocVecIterator {
			index: 0,
			data: self
		}
	}

	// temporary solution. implement into_iter
	pub fn remove_entry(&mut self, index: usize) -> (K, V) {
		self.data.remove(index)
	}
}

pub struct AssocVecIterator<'a, K, V> {
	index: usize,
	data: &'a AssocVec<K, V>
}

impl<'a, K: Eq + PartialEq, V> Iterator for AssocVecIterator<'a, K, V> {
	type Item = &'a (K, V);

	fn next(&mut self) -> Option<Self::Item> {
		if self.index < self.data.len() {
			let entry = &self.data.data[self.index];
			self.index += 1;
			Some(entry)
		} else {
			None
		}
	}
}