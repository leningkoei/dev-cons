my $msg = <STDIN>;
chomp $msg;
my $edge_line = "";
for (1..(length $msg) + 2) {
  $edge_line .= "+";
}
print $edge_line . "\n";
print "+" . $msg . "+" . "\n";
print $edge_line . "\n";
