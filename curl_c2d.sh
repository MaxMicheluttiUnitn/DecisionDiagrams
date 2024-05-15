#!/bin/bash  

echo "Enter your name: "  
read name
echo "Enter your e-mail: "
read email
echo "Enter your organization: "
read organization

echo $name
echo $email
echo $organization

curl -d 'os=Linux%20i386&n='$name'&e='$email'&o='$organization'' http://reasoning.cs.ucla.edu/c2d/fetchme.php --output c2d_linux.zip
unzip c2d_linux.zip

rm c2d_linux.zip