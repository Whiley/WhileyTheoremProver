// Copyright 2011 The Whiley Project Developers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wyal.util;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

import wyal.lang.Domain;
import wyal.lang.WyalFile.Declaration.Named;
import wyal.util.NameResolver;
import wyal.util.NameResolver.ResolutionError;

import static wyal.lang.WyalFile.*;

/**
 * The small world domain stems from the theory that all bugs can be found with
 * a "small world".
 *
 * @author David J. Pearce
 *
 */
public class SmallWorldDomain implements Domain {
	private final int intLowerBound = -3;
	private final int intUpperBound = 5;
	private final int arrayLengthBound = 2;
	private final int depthBound = 2;
	protected final NameResolver resolver;

	public SmallWorldDomain(NameResolver resolver) {
		this.resolver = resolver;
	}

	@Override
	public Generator generator(Type type) {
		return generator(type,0);
	}

	private Generator generator(Type type, int depth) {
		return generator(type, depth, new HashSet<>());
	}

	private Generator generator(Type type, int depth, Set<Name> visited) {
		// TODO: this could be made more efficient using a bitset instead of the
		// HashSet<Name> for visited. Could also avoid cloning in the non-contained
		// case.
		if(depth >= depthBound) {
			return VOID_GENERATOR;
		} else if (type instanceof Type.Null) {
			return new NullGenerator();
		} else if (type instanceof Type.Bool) {
			return new BoolGenerator();
		} else if (type instanceof Type.Int) {
			return new IntGenerator(intLowerBound, intUpperBound);
		} else if (type instanceof Type.Record) {
			Type.Record record = (Type.Record) type;
			FieldDeclaration[] fields = record.getFields();
			Arrays.sort(fields,fieldComparator);
			Identifier[] fieldNames = new Identifier[fields.length];
			Domain.Generator[] generators = new Domain.Generator[fields.length];
			for (int i = 0; i != generators.length; ++i) {
				FieldDeclaration field = fields[i];
				fieldNames[i] = field.getVariableName();
				generators[i] = generator(field.getType(),depth,visited);
			}
			return new RecordGenerator(fieldNames,generators);
		} else if (type instanceof Type.Array) {
			Type elementType = ((Type.Array) type).getElement();
			Domain.Generator[] generators = new Domain.Generator[arrayLengthBound];
			for (int i = 0; i != generators.length; ++i) {
				generators[i] = generator(elementType,depth,visited);
			}
			return new ArrayGenerator(generators);
		} else if (type instanceof Type.Union) {
			Type.Union union = (Type.Union) type;
			Domain.Generator[] generators = new Domain.Generator[arrayLengthBound];
			for (int i = 0; i != generators.length; ++i) {
				generators[i] = generator(union.get(i),depth,visited);
			}
			return new UnionGenerator(generators);
		} else if(type instanceof Type.Nominal) {
			Type.Nominal nominal = (Type.Nominal) type;
			try {
				Named.Type decl = resolver.resolveExactly(nominal.getName(), Named.Type.class);
				Name name = decl.getName();
				// Check for recursive types
				HashSet<Name> nvisited = new HashSet<>();
				if(visited.contains(name)) {
					// Have previously visited this type. Therefore, increase recursive depth and
					// reset the visited relation to prevent types contained within this from
					// tripping it.
					depth = depth + 1;
				} else {
					// Haven't yet visited this type, so simply make a record.
					nvisited.addAll(visited);
				}
				nvisited.add(name);
				// Recursively generate for this type
				return  generator(decl.getVariableDeclaration().getType(), depth, nvisited);
			} catch (ResolutionError e) {
				throw new RuntimeException(e);
			}
		} else {
			throw new IllegalArgumentException("unknown type encountered: " + type);
		}
	}

	private static final Comparator<FieldDeclaration> fieldComparator = new Comparator<FieldDeclaration>() {

		@Override
		public int compare(FieldDeclaration o1, FieldDeclaration o2) {
			return o1.getVariableName().compareTo(o2.getVariableName());
		}

	};

	private static EmptyGenerator VOID_GENERATOR = new EmptyGenerator();

	private static class EmptyGenerator implements Domain.Generator {

		@Override
		public boolean hasNext() {
			return false;
		}

		@Override
		public Object get() {
			throw new IllegalArgumentException("invalid operation");
		}

		@Override
		public void next() {
		}

		@Override
		public void reset() {
		}
	}

	private static class NullGenerator implements Domain.Generator {

		@Override
		public boolean hasNext() {
			return false;
		}

		@Override
		public Object get() {
			return null;
		}

		@Override
		public void next() {
			throw new UnsupportedOperationException();
		}

		@Override
		public void reset() {}
	}

	private static class BoolGenerator implements Domain.Generator {
		private int count;

		@Override
		public boolean hasNext() {
			return count <= 1;
		}

		@Override
		public Object get() {
			if(count == 0) {
				return false;
			} else {
				return true;
			}
		}

		@Override
		public void next() {
			count = count + 1;
		}

		@Override
		public void reset() {
			count = 0;
		}

	}

	private static class IntGenerator implements Domain.Generator {
		private final int max;
		private final int upperBound;
		private int count;

		public IntGenerator(int lowerBound, int upperBound) {
			this.max = upperBound - lowerBound;
			this.upperBound = upperBound;
			this.count = 0;
		}

		@Override
		public boolean hasNext() {
			return count <= max;
		}

		@Override
		public Object get() {
			int val = count <= upperBound ? count : -(count-upperBound);
			return BigInteger.valueOf(val);
		}

		@Override
		public void next() {
			count = count + 1;
		}

		@Override
		public void reset() {
			count = 0;
		}

	}

	private static class ArrayGenerator implements Domain.Generator {
		private final Domain.Generator[] generators;
		private int length;

		public ArrayGenerator(Domain.Generator[] generators) {
			this.generators = generators;
			this.length = 0;
		}

		@Override
		public boolean hasNext() {
			return length < generators.length;
		}

		@Override
		public Object get() {
			Object[] array = new Object[length];
			for(int i=0;i!=length;++i) {
				array[i] = generators[i].get();
			}
			return array;
		}

		@Override
		public void next() {
			for(int i=0;i!=length;++i) {
				Domain.Generator gen = generators[i];
				if(gen.hasNext()) {
					gen.next();
					return;
				} else {
					gen.reset();
				}
			}
			// If we get here then we have exhausted all arrays upto the given
			// length.
			length = length + 1;
		}

		@Override
		public void reset() {
			for(int i=0;i!=generators.length;++i) {
				generators[i].reset();
			}
			this.length = 0;
		}

	}

	private static class RecordGenerator implements Domain.Generator {
		private final Identifier[] fields;
		private final Domain.Generator[] generators;
		private boolean done;

		public RecordGenerator(Identifier[] fields, Domain.Generator[] generators) {
			this.fields = fields;
			this.generators = generators;
		}

		@Override
		public boolean hasNext() {
			if(done) {
				return false;
			} else {
				for(int i=0;i!=generators.length;++i) {
					if(!generators[i].hasNext()) {
						return false;
					}
				}
				return true;
			}
		}

		@Override
		public Object get() {
			Object[] array = new Object[generators.length];
			for(int i=0;i!=generators.length;++i) {
				array[i] = generators[i].get();
			}
			return new Interpreter.Record(fields,array);
		}

		@Override
		public void next() {
			for (int i = 0; i != generators.length; ++i) {
				Domain.Generator gen = generators[i];
				gen.next();
				if (gen.hasNext()) {
					return;
				} else {
					gen.reset();
				}
			}
			// If we get here then we have exhausted all arrays upto the given
			// length.
			done = true;
		}

		@Override
		public void reset() {
			for(int i=0;i!=generators.length;++i) {
				generators[i].reset();
			}
			this.done = false;
		}

	}


	private static class UnionGenerator implements Domain.Generator {
		private final Domain.Generator[] generators;
		private int index;

		public UnionGenerator(Domain.Generator[] generators) {
			for(int i=0;i!=generators.length;++i) {
				if(generators[i] == null) {
					throw new IllegalArgumentException("generator cannot be null");
				}
			}
			this.generators = generators;
			this.index = 0;
		}

		@Override
		public boolean hasNext() {
			// Skip over any empty generators
			while(index < generators.length && !generators[index].hasNext()) {
				index = index + 1;
			}
			//
			return index < generators.length;
		}

		@Override
		public Object get() {
			return generators[index].get();
		}

		@Override
		public void next() {
			while(!generators[index].hasNext()) {
				index = index + 1;
			}
			generators[index].next();
		}

		@Override
		public void reset() {
			for(int i=0;i!=generators.length;++i) {
				generators[i].reset();
			}
			this.index = 0;
		}

	}
}
