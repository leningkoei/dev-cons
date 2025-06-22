# my $greeting = "Hello world";
# my $count = <STDIN>;
# 
# for (1 .. $count) {
#   print $greeting . "\n";
# }

sub add {
  my (@array, $x, $y) = @_;
  print @array;
  print "\n";
  return $x + $y;
}

print add((1, 2, 3, 4), 3, 5);
print "\n";
