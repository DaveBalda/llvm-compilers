; ModuleID = 'Foo.ll'
source_filename = "Foo.ll"

define dso_local i32 @foo(i32 noundef %0, i32 noundef %1) {
  %3 = add nsw i32 %1, 1
  %4 = shl i32 %3, 1
  %5 = shl i32 %0, 1
  %6 = lshr i32 %5, 2
  %7 = mul nsw i32 %4, %6
  ret i32 %7
}
