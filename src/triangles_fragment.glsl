uniform vec3 lightPos;
uniform float specular, shininess;

in vec3 normal, halfVector;
in vec4 diffuse, ambient, m_position;

out vec4 FragColor;

void main(){
  vec3 halfV, lightDir;
  float NdotL, NdotHV;

  lightDir = normalize(lightPos - m_position.xyz);

  // The ambient term will always be present.
  vec4 color = ambient;

  // compute the dot product between normal and ldir.
  NdotL = abs(dot(normal, lightDir));
  color += diffuse * NdotL;
  halfV = normalize(halfVector);
  NdotHV = abs(dot(normal, halfV));
  color += specular * pow(NdotHV, shininess);

  FragColor = color;
}
